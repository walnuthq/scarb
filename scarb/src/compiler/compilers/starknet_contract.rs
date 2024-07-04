use anyhow::{bail, ensure, Context, Result};
use cairo_lang_compiler::db::RootDatabase;
use cairo_lang_defs::ids::NamedLanguageElementId;
use cairo_lang_diagnostics::ToOption;
use cairo_lang_filesystem::db::{get_originating_location, AsFilesGroupMut, FilesGroup};
use cairo_lang_filesystem::flag::Flag;
use cairo_lang_filesystem::ids::{CrateId, CrateLongId, FileId, FileLongId, FlagId, VirtualFile};
use cairo_lang_filesystem::span::TextSpan;
use cairo_lang_semantic::db::SemanticGroup;
use cairo_lang_sierra_generator::db::SierraGenGroup;
use cairo_lang_sierra_generator::program_generator::{
    SierraProgramDebugInfo, SierraProgramWithDebug,
};
use cairo_lang_starknet::compile::{
    compile_prepared_db, extract_semantic_entrypoints, SemanticEntryPoints,
};
use cairo_lang_starknet::contract::{find_contracts, ContractDeclaration};
use cairo_lang_starknet_classes::allowed_libfuncs::{
    AllowedLibfuncsError, ListSelector, BUILTIN_EXPERIMENTAL_LIBFUNCS_LIST,
};
use cairo_lang_starknet_classes::casm_contract_class::CasmContractClass;
use cairo_lang_starknet_classes::contract_class::ContractClass;
use cairo_lang_utils::{Upcast, UpcastMut};
use indoc::{formatdoc, writedoc};
use itertools::{chain, izip, Itertools};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt::Write;
use std::iter::zip;
use std::sync::Arc;
use tracing::{debug, trace, trace_span};

use crate::compiler::helpers::{build_compiler_config, collect_main_crate_ids, write_json};
use crate::compiler::{CairoCompilationUnit, CompilationUnitAttributes, Compiler};
use crate::core::{PackageName, TargetKind, Utf8PathWorkspaceExt, Workspace};
use crate::internal::serdex::RelativeUtf8PathBuf;
use scarb_stable_hash::short_hash;

const CAIRO_PATH_SEPARATOR: &str = "::";
const GLOB_PATH_SELECTOR: &str = "*";

// TODO(#111): starknet-contract should be implemented as an extension.
pub struct StarknetContractCompiler;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
struct Props {
    pub sierra: bool,
    pub casm: bool,
    pub casm_add_pythonic_hints: bool,
    pub allowed_libfuncs: bool,
    pub allowed_libfuncs_deny: bool,
    pub allowed_libfuncs_list: Option<SerdeListSelector>,
    pub build_external_contracts: Option<Vec<ContractSelector>>,
}

impl Default for Props {
    fn default() -> Self {
        Self {
            sierra: true,
            casm: false,
            casm_add_pythonic_hints: false,
            allowed_libfuncs: true,
            allowed_libfuncs_deny: false,
            allowed_libfuncs_list: None,
            build_external_contracts: None,
        }
    }
}

// FIXME(#401): Make allowed-libfuncs-list.path relative to current Scarb.toml rather than PWD.
#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged, rename_all = "kebab-case")]
pub enum SerdeListSelector {
    Name { name: String },
    Path { path: RelativeUtf8PathBuf },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ContractSelector(String);

impl ContractSelector {
    fn package(&self) -> PackageName {
        let parts = self
            .0
            .split_once(CAIRO_PATH_SEPARATOR)
            .unwrap_or((self.0.as_str(), ""));
        PackageName::new(parts.0)
    }

    fn contract(&self) -> String {
        let parts = self
            .0
            .rsplit_once(CAIRO_PATH_SEPARATOR)
            .unwrap_or((self.0.as_str(), ""));
        parts.1.to_string()
    }

    fn is_wildcard(&self) -> bool {
        self.0.ends_with(GLOB_PATH_SELECTOR)
    }

    fn partial_path(&self) -> String {
        let parts = self
            .0
            .split_once(GLOB_PATH_SELECTOR)
            .unwrap_or((self.0.as_str(), ""));
        parts.0.to_string()
    }

    fn full_path(&self) -> String {
        self.0.clone()
    }
}

struct ContractFileStemCalculator(HashSet<String>);

impl ContractFileStemCalculator {
    fn new(contract_paths: Vec<String>) -> Self {
        let mut seen = HashSet::new();
        let contract_name_duplicates = contract_paths
            .iter()
            .map(|it| ContractSelector(it.clone()).contract())
            .filter(|contract_name| {
                // insert returns false for duplicate values
                !seen.insert(contract_name.clone())
            })
            .collect::<HashSet<String>>();
        Self(contract_name_duplicates)
    }

    fn get_stem(&mut self, full_path: String) -> String {
        let contract_selector = ContractSelector(full_path);
        let contract_name = contract_selector.contract();

        if self.0.contains(&contract_name) {
            contract_selector
                .full_path()
                .replace(CAIRO_PATH_SEPARATOR, "_")
        } else {
            contract_name
        }
    }
}

#[derive(Debug, Serialize)]
struct StarknetArtifacts {
    version: usize,
    contracts: Vec<ContractArtifacts>,
}

impl Default for StarknetArtifacts {
    fn default() -> Self {
        Self {
            version: 1,
            contracts: Vec::new(),
        }
    }
}

impl StarknetArtifacts {
    fn finish(&mut self) {
        assert!(
            self.contracts.iter().map(|it| &it.id).all_unique(),
            "Artifacts IDs must be unique."
        );

        self.contracts.sort_unstable_by_key(|it| it.id.clone());
    }
}

#[derive(Debug, Serialize)]
struct ContractArtifacts {
    id: String,
    package_name: PackageName,
    contract_name: String,
    module_path: String,
    artifacts: ContractArtifact,
}

impl ContractArtifacts {
    fn new(
        package_name: &PackageName,
        contract_name: &str,
        contract_path: &str,
        module_path: &str,
    ) -> Self {
        Self {
            id: short_hash((&package_name, &contract_path)),
            package_name: package_name.clone(),
            contract_name: contract_name.to_owned(),
            module_path: module_path.to_owned(),
            artifacts: ContractArtifact::default(),
        }
    }
}

#[derive(Debug, Default, Serialize)]
struct ContractArtifact {
    sierra: Option<String>,
    casm: Option<String>,
}

const AUTO_WITHDRAW_GAS_FLAG: &str = "add_withdraw_gas";

impl Compiler for StarknetContractCompiler {
    fn target_kind(&self) -> TargetKind {
        TargetKind::STARKNET_CONTRACT.clone()
    }

    fn compile(
        &self,
        unit: CairoCompilationUnit,
        db: &mut RootDatabase,
        ws: &Workspace<'_>,
    ) -> Result<()> {
        let props: Props = unit.target().props()?;
        if !props.sierra && !props.casm {
            ws.config().ui().warn(
                "both Sierra and CASM Starknet contract targets have been disabled, \
                Scarb will not produce anything",
            );
        }

        ensure_gas_enabled(db)?;

        if let Some(external_contracts) = props.build_external_contracts.clone() {
            for path in external_contracts.iter() {
                ensure!(path.0.matches(GLOB_PATH_SELECTOR).count() <= 1,
                    "external contract path {} has multiple global path selectors, only one '*' selector is allowed",
                    path.0);
            }
        }

        let target_dir = unit.target_dir(ws);

        let compiler_config = build_compiler_config(&unit, ws);

        let main_crate_ids = collect_main_crate_ids(&unit, db);

        let contracts = find_project_contracts(
            db.upcast_mut(),
            main_crate_ids,
            props.build_external_contracts.clone(),
        )?;

        let contract_paths = contracts
            .iter()
            .map(|decl| decl.module_id().full_path(db.upcast_mut()))
            .collect::<Vec<_>>();
        trace!(contracts = ?contract_paths);

        let contracts = contracts.iter().collect::<Vec<_>>();

        let classes = {
            let _ = trace_span!("compile_starknet").enter();
            compile_prepared_db(db, &contracts, compiler_config)?
        };

        let classes_debug_info = compile_prepared_db_to_debug_info(db, &contracts)?;

        check_allowed_libfuncs(&props, &contracts, &classes, db, &unit, ws)?;

        let casm_classes: Vec<Option<CasmContractClass>> = if props.casm {
            let _ = trace_span!("compile_sierra").enter();
            zip(&contracts, &classes)
                .map(|(decl, class)| -> Result<_> {
                    let contract_name = decl.submodule_id.name(db.upcast_mut());
                    let casm_class = CasmContractClass::from_contract_class(
                        class.clone(),
                        props.casm_add_pythonic_hints,
                        usize::MAX,
                    )
                    .with_context(|| {
                        format!("{contract_name}: failed to compile Sierra contract to CASM")
                    })?;
                    Ok(Some(casm_class))
                })
                .try_collect()?
        } else {
            classes.iter().map(|_| None).collect()
        };

        let mut artifacts = StarknetArtifacts::default();
        let mut file_stem_calculator = ContractFileStemCalculator::new(contract_paths);

        let target_name = &unit.target().name;
        for (decl, class, casm_class, class_debug_info) in
            izip!(contracts, classes, casm_classes, classes_debug_info)
        {
            let contract_name = decl.submodule_id.name(db.upcast_mut());
            let contract_path = decl.module_id().full_path(db.upcast_mut());

            let contract_selector = ContractSelector(contract_path);
            let package_name = contract_selector.package();
            let contract_stem = file_stem_calculator.get_stem(contract_selector.full_path());

            let file_stem = format!("{target_name}_{contract_stem}");

            let mut artifact = ContractArtifacts::new(
                &package_name,
                &contract_name,
                contract_selector.full_path().as_str(),
                &decl.module_id().full_path(db.upcast_mut()),
            );

            if props.sierra {
                let file_name = format!("{file_stem}.contract_class.json");
                write_json(&file_name, "output file", &target_dir, ws, &class)?;
                artifact.artifacts.sierra = Some(file_name);

                let sierra_to_cairo_debug_info =
                    get_sierra_to_cairo_debug_info(&class_debug_info, &db);
                let file_name = format!("{file_stem}.contract_class_debug.json");
                write_json(
                    &file_name,
                    "output file",
                    &target_dir,
                    ws,
                    &sierra_to_cairo_debug_info,
                )?;
            }

            // if props.casm
            if let Some(casm_class) = casm_class {
                let file_name = format!("{file_stem}.compiled_contract_class.json");
                write_json(&file_name, "output file", &target_dir, ws, &casm_class)?;
                artifact.artifacts.casm = Some(file_name);
            }

            artifacts.contracts.push(artifact);
        }

        artifacts.finish();

        write_json(
            &format!("{}.starknet_artifacts.json", target_name),
            "starknet artifacts file",
            &target_dir,
            ws,
            &artifacts,
        )?;

        Ok(())
    }
}

fn ensure_gas_enabled(db: &mut RootDatabase) -> Result<()> {
    let flag = FlagId::new(db.as_files_group_mut(), AUTO_WITHDRAW_GAS_FLAG);
    let flag = db.get_flag(flag);
    ensure!(
        flag.map(|f| matches!(*f, Flag::AddWithdrawGas(true)))
            .unwrap_or(false),
        "the target starknet contract compilation requires gas to be enabled"
    );
    Ok(())
}

fn find_project_contracts(
    mut db: &dyn SemanticGroup,
    main_crate_ids: Vec<CrateId>,
    external_contracts: Option<Vec<ContractSelector>>,
) -> Result<Vec<ContractDeclaration>> {
    let internal_contracts = {
        let _ = trace_span!("find_internal_contracts").enter();
        find_contracts(db, &main_crate_ids)
    };

    let external_contracts: Vec<ContractDeclaration> =
        if let Some(external_contracts) = external_contracts {
            let _ = trace_span!("find_external_contracts").enter();
            debug!("external contracts selectors: {:?}", external_contracts);

            let crate_ids = external_contracts
                .iter()
                .map(|selector| selector.package().into())
                .unique()
                .map(|package_name: SmolStr| {
                    db.upcast_mut()
                        .intern_crate(CrateLongId::Real(package_name))
                })
                .collect::<Vec<_>>();
            let contracts = find_contracts(db, crate_ids.as_ref());
            let filtered_contracts: Vec<ContractDeclaration> = contracts
                .into_iter()
                .filter(|decl| {
                    let contract_path = decl.module_id().full_path(db.upcast());
                    external_contracts.iter().any(|selector| {
                        if selector.is_wildcard() {
                            contract_path.starts_with(&selector.partial_path())
                        } else {
                            contract_path == selector.full_path()
                        }
                    })
                })
                .collect();

            filtered_contracts
        } else {
            debug!("no external contracts selected");
            Vec::new()
        };

    Ok(internal_contracts
        .into_iter()
        .chain(external_contracts)
        .collect())
}

fn check_allowed_libfuncs(
    props: &Props,
    contracts: &[&ContractDeclaration],
    classes: &[ContractClass],
    db: &RootDatabase,
    unit: &CairoCompilationUnit,
    ws: &Workspace<'_>,
) -> Result<()> {
    if !props.allowed_libfuncs {
        debug!("allowed libfuncs checking disabled by target props");
        return Ok(());
    }

    let list_selector = match &props.allowed_libfuncs_list {
        Some(SerdeListSelector::Name { name }) => ListSelector::ListName(name.clone()),
        Some(SerdeListSelector::Path { path }) => {
            let path = path.relative_to_file(unit.main_component().package.manifest_path())?;
            ListSelector::ListFile(path.into_string())
        }
        None => Default::default(),
    };

    let mut found_disallowed = false;
    for (decl, class) in zip(contracts, classes) {
        match class.validate_version_compatible(list_selector.clone()) {
            Ok(()) => {}

            Err(AllowedLibfuncsError::UnsupportedLibfunc {
                invalid_libfunc,
                allowed_libfuncs_list_name,
            }) => {
                found_disallowed = true;

                let contract_name = decl.submodule_id.name(db.upcast());
                let mut diagnostic = formatdoc! {r#"
                    libfunc `{invalid_libfunc}` is not allowed in the libfuncs list `{allowed_libfuncs_list_name}`
                     --> contract: {contract_name}
                "#};

                // If user did not explicitly specify the allowlist, show a help message
                // instructing how to do this. Otherwise, we know that user knows what they
                // do, so we do not clutter compiler output.
                if list_selector == Default::default() {
                    let experimental = BUILTIN_EXPERIMENTAL_LIBFUNCS_LIST;

                    let scarb_toml = unit
                        .main_component()
                        .package
                        .manifest_path()
                        .workspace_relative(ws);

                    let _ = writedoc!(
                        &mut diagnostic,
                        r#"
                            help: try compiling with the `{experimental}` list
                             --> {scarb_toml}
                                [[target.starknet-contract]]
                                allowed-libfuncs-list.name = "{experimental}"
                        "#
                    );
                }

                if props.allowed_libfuncs_deny {
                    ws.config().ui().error(diagnostic);
                } else {
                    ws.config().ui().warn(diagnostic);
                }
            }

            Err(e) => {
                return Err(e).with_context(|| {
                    format!(
                        "failed to check allowed libfuncs for contract: {contract_name}",
                        contract_name = decl.submodule_id.name(db.upcast())
                    )
                })
            }
        }
    }

    if found_disallowed && props.allowed_libfuncs_deny {
        bail!("aborting compilation, because contracts use disallowed Sierra libfuncs");
    }

    Ok(())
}

pub fn compile_prepared_db_to_debug_info(
    db: &RootDatabase,
    contracts: &[&ContractDeclaration],
    // mut compiler_config: CompilerConfig<'_>,
) -> Result<Vec<SierraProgramDebugInfo>> {
    // compiler_config.diagnostics_reporter.ensure(db)?;

    contracts
        .iter()
        .map(|contract| compile_contract_with_prepared_and_checked_db_to_debug_info(db, contract))
        .try_collect()
}

/// Compile declared Starknet contract.
///
/// The `contract` value **must** come from `db`, for example as a result of calling
/// [`find_contracts`]. Does not check diagnostics, it is expected that they are checked by caller
/// of this function.
fn compile_contract_with_prepared_and_checked_db_to_debug_info(
    db: &RootDatabase,
    contract: &ContractDeclaration,
) -> Result<SierraProgramDebugInfo> {
    let SemanticEntryPoints {
        external,
        l1_handler,
        constructor,
    } = extract_semantic_entrypoints(db, contract)?;
    let SierraProgramWithDebug {
        program: mut sierra_program,
        debug_info,
    } = Arc::unwrap_or_clone(
        db.get_sierra_program_for_functions(
            chain!(&external, &l1_handler, &constructor)
                .map(|f| f.value)
                .collect(),
        )
        .to_option()
        .with_context(|| "Compilation failed without any diagnostics.")?,
    );

    Ok(debug_info)

    // if compiler_config.replace_ids {
    //     sierra_program = replace_sierra_ids_in_program(db, &sierra_program);
    // }
    // let replacer = CanonicalReplacer::from_program(&sierra_program);
    // let sierra_program = replacer.apply(&sierra_program);

    // // let entry_points_by_type = ContractEntryPoints {
    // //     external: get_entry_points(db, &external, &replacer)?,
    // //     l1_handler: get_entry_points(db, &l1_handler, &replacer)?,
    // //     // Later generation of ABI verifies that there is up to one constructor.
    // //     constructor: get_entry_points(db, &constructor, &replacer)?,
    // // };

    // let annotations = if compiler_config.add_statements_functions {
    //     let statements_functions = debug_info
    //         .statements_locations
    //         .extract_statements_functions(db);
    //     Annotations::from(statements_functions)
    // } else {
    //     Default::default()
    // };

    // let contract_class = ContractClass::new(
    //     &sierra_program,
    //     entry_points_by_type,
    //     Some(
    //         AbiBuilder::from_submodule(db, contract.submodule_id, Default::default())
    //             .ok()
    //             .with_context(|| "Unexpected error while generating ABI.")?
    //             .finalize()
    //             .with_context(|| "Could not create ABI from contract submodule")?,
    //     ),
    //     annotations,
    // )?;
    // contract_class.sanity_check();
    // Ok(contract_class)
}

// /// Returns the entry points given their IDs sorted by selectors.
// fn get_entry_points(
//     db: &RootDatabase,
//     entry_point_functions: &[Aliased<ConcreteFunctionWithBodyId>],
//     replacer: &CanonicalReplacer,
// ) -> Result<Vec<ContractEntryPoint>> {
//     let mut entry_points = vec![];
//     for function_with_body_id in entry_point_functions {
//         let (selector, sierra_id) =
//             get_selector_and_sierra_function(db, function_with_body_id, replacer);

//         entry_points.push(ContractEntryPoint {
//             selector: selector.to_biguint(),
//             function_idx: sierra_id.id as usize,
//         });
//     }
//     entry_points.sort_by(|a, b| a.selector.cmp(&b.selector));
//     Ok(entry_points)
// }

#[derive(Debug, Serialize)]
pub struct SierraToCairoDebugInfo {
    pub sierra_statements_to_cairo_info: HashMap<usize, SierraStatementToCairoDebugInfo>,
}

/// Human readable position inside a file, in lines and characters.
#[derive(Debug, Serialize, Clone)]
pub struct TextPosition {
    /// Line index, 0 based.
    pub line: usize,
    /// Character index inside the line, 0 based.
    pub col: usize,
}

#[derive(Debug, Serialize, Clone)]
pub struct Location {
    pub start: TextPosition,
    pub end: TextPosition,
    pub file_path: String,
}

#[derive(Debug, Serialize)]
pub struct SierraStatementToCairoDebugInfo {
    pub cairo_locations: Vec<Location>,
}

/// Returns a map from Sierra statement indexes to Cairo function names.
pub fn get_sierra_to_cairo_debug_info(
    sierra_program_debug_info: &SierraProgramDebugInfo,
    compiler_db: &RootDatabase,
) -> SierraToCairoDebugInfo {
    let mut sierra_statements_to_cairo_info: HashMap<usize, SierraStatementToCairoDebugInfo> =
        HashMap::new();

    for (statement_idx, location) in sierra_program_debug_info
        .statements_locations
        .locations
        .iter_sorted()
    {
        let mut cairo_locations: Vec<Location> = Vec::new();
        // for location in locations {
        let syntax_node = location.syntax_node(compiler_db);
        let mut file_id = syntax_node.stable_ptr().file_id(compiler_db);
        let file_name = file_id.file_name(compiler_db);
        let mut syntax_node_location_span = syntax_node.span_without_trivia(compiler_db);

        // let (originating_file_id, originating_text_span) =
        // get_originating_location(compiler_db, file_id, syntax_node_location_span);

        let cairo_location =
            get_location_from_text_span(syntax_node_location_span, file_id, compiler_db);
        if cairo_location.is_some() {
            cairo_locations.push(cairo_location.unwrap());
        }
        while let FileLongId::Virtual(VirtualFile {
            parent: Some(parent),
            code_mappings,
            ..
        }) = compiler_db.lookup_intern_file(file_id)
        {
            if let Some(origin) = code_mappings
                .iter()
                .find_map(|mapping| mapping.translate(syntax_node_location_span))
            {
                syntax_node_location_span = origin;
                file_id = parent;
                let cairo_location =
                    get_location_from_text_span(syntax_node_location_span, file_id, compiler_db);
                if cairo_location.is_some() {
                    cairo_locations.push(cairo_location.unwrap());
                }
            } else {
                break;
            }
        }

        // let cairo_location =
        //     get_location_from_text_span(originating_text_span, originating_file_id, compiler_db);
        // if cairo_location.is_some() {
        //     cairo_locations.push(cairo_location.unwrap());
        // }
        // }
        sierra_statements_to_cairo_info.insert(
            statement_idx.0,
            SierraStatementToCairoDebugInfo { cairo_locations },
        );
    }

    SierraToCairoDebugInfo {
        sierra_statements_to_cairo_info,
    }
}

pub fn get_location_from_text_span(
    text_span: TextSpan,
    file_id: FileId,
    compiler_db: &RootDatabase,
) -> Option<Location> {
    let current_dir = env::current_dir().expect("Failed to get current directory");
    // dbg!(&current_dir);
    // let file_path = match compiler_db.lookup_intern_file(file_id) {
    //     FileLongId::OnDisk(path) => {
    //         path.strip_prefix(current_dir).expect("Failed to get relative path").to_path_buf().to_str().unwrap_or("<unknown>").to_string()
    //     },
    //     FileLongId::Virtual(_) => file_id.full_path(compiler_db),
    // };
    let file_path = match compiler_db.lookup_intern_file(file_id) {
        FileLongId::OnDisk(path) => match path.strip_prefix(&current_dir) {
            Ok(relative_path) => relative_path.to_str().unwrap_or("<unknown>").to_string(),
            Err(_) => {
                return None;
            }
        },
        FileLongId::Virtual(_) => {
            return None;
        }
    };

    // let file_path = file_id.full_path(compiler_db);

    let start: Option<TextPosition> =
        text_span
            .start
            .position_in_file(compiler_db, file_id)
            .map(|s| TextPosition {
                line: s.line,
                col: s.col,
            });

    let end = text_span
        .end
        .position_in_file(compiler_db, file_id)
        .map(|e| TextPosition {
            line: e.line,
            col: e.col,
        });

    start.zip(end).map(|(start, end)| Location {
        start,
        end,
        file_path,
    })
}

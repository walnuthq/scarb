#![deny(missing_docs)]

//! CLI arguments datastructures.

use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use scarb::metadata::MetadataVersion;

/// Cairo's project manager.
#[derive(Parser, Clone, Debug)]
#[command(author, version, about)]
pub struct Args {
    /// Override path to a directory containing a **Scarb.toml** file.
    #[arg(long, env = "SCARB_MANIFEST_PATH")]
    pub manifest_path: Option<PathBuf>,

    /// Logging verbosity.
    #[command(flatten)]
    pub verbose: clap_verbosity_flag::Verbosity,

    /// Subcommand and its arguments.
    #[command(subcommand)]
    pub command: Command,
}

/// Subcommand and its arguments.
#[derive(Subcommand, Clone, Debug)]
pub enum Command {
    // Keep these sorted alphabetically.
    // External should go last.
    /// Add dependencies to a manifest file.
    Add,
    /// Compile current project.
    Build,
    /// Remove generated artifacts.
    Clean,
    /// List installed commands.
    Commands,
    /// Print path to current **Scarb.toml** file to standard output.
    ManifestPath,
    /// Output the resolved dependencies of a package, the concrete used versions including
    /// overrides, in machine-readable format.
    Metadata(MetadataArgs),

    /// External command (`scarb-*` executable).
    #[command(external_subcommand)]
    External(Vec<OsString>),
}

/// Arguments accepted by the `metadata` command.
#[derive(Parser, Clone, Debug)]
pub struct MetadataArgs {
    // Format version.
    #[arg(long, value_name = "VERSION")]
    pub format_version: MetadataVersion,
    /// Output information only about the workspace members and don't fetch dependencies.
    #[arg(long)]
    pub no_deps: bool,
}
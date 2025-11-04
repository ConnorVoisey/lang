use clap::{Args, Parser, Subcommand, ValueEnum};

#[derive(Debug, Parser)]
#[command(name = "lang")]
#[command(about = "Compiler for the lang language", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Debug, Subcommand)]
pub enum Commands {
    /// Compile src code
    #[command(arg_required_else_help = true)]
    Build { path: String },

    /// Check and validate src code, Not yet implemented
    #[command(arg_required_else_help = true)]
    Check { path: String },
}

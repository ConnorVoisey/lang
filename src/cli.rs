use clap::{Parser, Subcommand, ValueEnum};

#[derive(Debug, Parser)]
#[command(name = "lang")]
#[command(about = "Compiler for the lang language", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,

    /// Output chrome tracing json file
    #[arg(short, long, default_value_t = false)]
    pub chrome_tracing: bool,

    /// set tracing level
    #[arg(short, long, default_value_t = LogLevel::Info)]
    pub log_level: LogLevel,
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

#[derive(ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

impl LogLevel {
    pub fn to_tracing_level(&self) -> tracing::Level {
        match self {
            LogLevel::Trace => tracing::Level::TRACE,
            LogLevel::Debug => tracing::Level::DEBUG,
            LogLevel::Info => tracing::Level::INFO,
            LogLevel::Warn => tracing::Level::WARN,
            LogLevel::Error => tracing::Level::ERROR,
        }
    }
}

impl std::fmt::Display for LogLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_possible_value()
            .expect("no values are skipped")
            .get_name()
            .fmt(f)
    }
}

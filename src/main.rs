use clap::Parser;
use lang::{
    ModParser,
    cli::Cli,
    interner::{Interner, SharedInterner},
};
use parking_lot::lock_api::RwLock;
use std::fs::read_to_string;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

fn main() -> color_eyre::Result<()> {
    let cli_args = Cli::parse();

    // set guard variable to live for entire program duration
    let _guard;
    let chrome_layer = if cli_args.chrome_tracing {
        let (layer, guard) = tracing_chrome::ChromeLayerBuilder::new().build();
        _guard = Some(guard);
        Some(layer)
    } else {
        _guard = None;
        None
    };

    let level_filter =
        tracing_subscriber::filter::LevelFilter::from_level(cli_args.log_level.to_tracing_level());

    tracing_subscriber::registry()
        .with(level_filter)
        .with(chrome_layer)
        .with(
            tracing_tree::HierarchicalLayer::new(2)
                .with_targets(true)
                .with_bracketed_fields(true),
        )
        .init();

    match cli_args.command {
        lang::cli::Commands::Build { path } => {
            let src_code = &read_to_string(&path).unwrap();
            let interner = Interner::new();
            let shared_interner = SharedInterner::new(RwLock::new(interner));
            match ModParser::parse_file(&path, &shared_interner) {
                Ok(v) => v,
                Err(e) => {
                    e.display(src_code, &path);
                    return Err(color_eyre::eyre::eyre!("Failed to compile module {e}"));
                }
            };
        }
        lang::cli::Commands::Check { path: _ } => {
            eprintln!("The `check` command is not yet implemented.");
            std::process::exit(1);
        }
    }

    Ok(())
}

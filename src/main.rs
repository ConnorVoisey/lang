use clap::Parser;
use lang::{
    ModParser,
    cli::Cli,
    interner::{Interner, SharedInterner},
};
use parking_lot::lock_api::RwLock;
use std::fs::read_to_string;
use tracing_subscriber::layer::SubscriberExt;

/// Set to false to use hierarchical console output
const USE_CHROME_TRACING: bool = true;

fn main() -> color_eyre::Result<()> {
    let cli_args = Cli::parse();
    let _guard;

    if USE_CHROME_TRACING {
        // View in chrome://tracing or ui.perfetto.dev
        let (chrome_layer, guard) = tracing_chrome::ChromeLayerBuilder::new().build();

        let subscriber = tracing_subscriber::registry().with(chrome_layer);

        tracing::subscriber::set_global_default(subscriber)?;

        _guard = guard;
    } else {
        use tracing_subscriber::util::SubscriberInitExt;

        tracing_subscriber::registry()
            .with(
                tracing_tree::HierarchicalLayer::new(2)
                    .with_targets(true)
                    .with_bracketed_fields(true),
            )
            .init();
    }
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
        t => {
            dbg!(t);
            todo!("handle other command cases");
        }
    }

    Ok(())
}

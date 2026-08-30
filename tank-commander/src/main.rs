//! CLI for the Tank Commander simulator.

use std::process::ExitCode;

use clap::{Parser, Subcommand};
use tank_commander::metrics::format_aggregate;
use tank_commander::sim::{self, SimConfig};

#[derive(Debug, Parser)]
#[command(
    name = "tank-commander",
    version,
    about = "Simulate Tank Commander Skirmish games for balance and fun metrics"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Run many Skirmish games and print drama / stalemate aggregates.
    Sim {
        /// Number of games to play.
        #[arg(long, default_value_t = 200)]
        games: u32,
        /// Base RNG seed (game i uses seed+i).
        #[arg(long, default_value_t = 1)]
        seed: u64,
        /// Print a full event log for the first game.
        #[arg(long, default_value_t = false)]
        verbose: bool,
        /// Also emit the aggregate report as JSON on stdout after the text.
        #[arg(long, default_value_t = false)]
        json: bool,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Commands::Sim {
            games,
            seed,
            verbose,
            json,
        } => {
            let result = sim::run(SimConfig {
                games,
                seed,
                verbose,
            });
            if verbose {
                println!("=== sample game (seed {seed}) ===");
                for line in &result.sample_events {
                    println!("{line}");
                }
                println!();
            }
            print!("{}", format_aggregate(&result.aggregate));
            if json {
                match serde_json::to_string_pretty(&result.aggregate) {
                    Ok(s) => println!("\n{s}"),
                    Err(e) => {
                        eprintln!("json encode failed: {e}");
                        return ExitCode::FAILURE;
                    }
                }
            }
        }
    }
    ExitCode::SUCCESS
}

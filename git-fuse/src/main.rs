use std::path::PathBuf;
use std::process::exit;
use std::time::Duration;

use clap::Parser;

const AFTER_HELP: &str = "\
LAYOUT:
    <mountpoint>/refs/<ref>            file containing the ref's sha
    <mountpoint>/refs/HEAD             sha of the default branch
    <mountpoint>/commits/<sha>/<path>  any commit's tree as plain files

Runs in the foreground; unmount with Ctrl-C or `fusermount3 -u <mountpoint>`.";

/// Mount a git-server repository as a read-only filesystem.
#[derive(Parser)]
#[command(name = "git-fuse", version, after_help = AFTER_HELP)]
struct Cli {
    /// The clone URL, e.g. https://host/<repo>
    #[arg(value_name = "REMOTE-URL")]
    remote_url: String,

    /// An empty directory to mount the repository on
    #[arg(value_name = "MOUNTPOINT")]
    mountpoint: PathBuf,

    /// Local bare-repo cache (default: ~/.cache/git-fuse/…, shared across
    /// mounts of the same remote)
    #[arg(long, value_name = "DIR")]
    cache_dir: Option<PathBuf>,

    /// How long ref lookups stay cached, in seconds
    #[arg(long, value_name = "SECS", default_value = "2", value_parser = parse_secs)]
    refs_ttl: Duration,

    /// Don't clone/fetch in the background; serve from the remote API plus
    /// whatever the cache already holds
    #[arg(long)]
    no_warmup: bool,

    /// Don't optimistically download full history: cache only the ref tips
    /// (plus new commits as tips move); older commits are served via the API
    /// on access and backfilled (snapshot first, then the intervening
    /// history) in the background. Saves disk/bandwidth
    #[arg(long)]
    lazy_history: bool,

    /// Let other users read the mount (needs user_allow_other in
    /// /etc/fuse.conf)
    #[arg(long)]
    allow_other: bool,

    /// Log activity to stderr
    #[arg(long)]
    verbose: bool,
}

fn parse_secs(s: &str) -> Result<Duration, String> {
    match s.parse::<f64>() {
        Ok(secs) if secs >= 0.0 => Ok(Duration::from_secs_f64(secs)),
        _ => Err("needs a non-negative number of seconds".to_owned()),
    }
}

fn main() {
    let (cli, ping) = whbiab::parse::<Cli>(env!("CARGO_PKG_VERSION"));
    let mut opts = git_fuse::Options::new(cli.remote_url);
    opts.cache_dir = cli.cache_dir;
    opts.refs_ttl = cli.refs_ttl;
    opts.warmup = !cli.no_warmup;
    opts.lazy_history = cli.lazy_history;
    opts.verbose = cli.verbose;
    opts.allow_other = cli.allow_other;

    let result = git_fuse::run(&cli.mountpoint, opts, true);
    ping.wait();
    if let Err(e) = result {
        eprintln!("git-fuse: {e}");
        exit(1);
    }
}

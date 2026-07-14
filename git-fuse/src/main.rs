use std::path::PathBuf;
use std::process::exit;
use std::time::Duration;

const USAGE: &str = "\
git-fuse: mount a git-server repository as a read-only filesystem

USAGE:
    git-fuse [OPTIONS] <REMOTE-URL> <MOUNTPOINT>

    <REMOTE-URL> is the clone URL, e.g. https://host/<repo>

LAYOUT:
    <mountpoint>/refs/<ref>            file containing the ref's sha
    <mountpoint>/refs/HEAD             sha of the default branch
    <mountpoint>/commits/<sha>/<path>  any commit's tree as plain files

OPTIONS:
    --cache-dir <DIR>   local bare-repo cache (default: ~/.cache/git-fuse/…,
                        shared across mounts of the same remote)
    --refs-ttl <SECS>   how long ref lookups stay cached (default: 2)
    --no-warmup         don't clone/fetch in the background; serve from the
                        remote API plus whatever the cache already holds
    --allow-other       let other users read the mount (needs
                        user_allow_other in /etc/fuse.conf)
    --verbose           log activity to stderr
    -h, --help          show this help

Runs in the foreground; unmount with Ctrl-C or `fusermount3 -u <mountpoint>`.
";

fn fail(msg: &str) -> ! {
    eprintln!("git-fuse: {msg}\n\n{USAGE}");
    exit(2);
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut positional: Vec<String> = Vec::new();
    let mut cache_dir: Option<PathBuf> = None;
    let mut refs_ttl = Duration::from_secs(2);
    let mut warmup = true;
    let mut verbose = false;
    let mut allow_other = false;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                print!("{USAGE}");
                return;
            }
            "--cache-dir" => match args.next() {
                Some(v) => cache_dir = Some(PathBuf::from(v)),
                None => fail("--cache-dir needs a value"),
            },
            "--refs-ttl" => match args.next().and_then(|v| v.parse::<f64>().ok()) {
                Some(secs) if secs >= 0.0 => refs_ttl = Duration::from_secs_f64(secs),
                _ => fail("--refs-ttl needs a non-negative number of seconds"),
            },
            "--no-warmup" => warmup = false,
            "--allow-other" => allow_other = true,
            "--verbose" => verbose = true,
            other if other.starts_with('-') => fail(&format!("unknown option {other}")),
            _ => positional.push(arg),
        }
    }

    let [remote_url, mountpoint] = positional.as_slice() else {
        fail("expected exactly two arguments: <REMOTE-URL> <MOUNTPOINT>");
    };
    let mut opts = git_fuse::Options::new(remote_url.clone());
    opts.cache_dir = cache_dir;
    opts.refs_ttl = refs_ttl;
    opts.warmup = warmup;
    opts.verbose = verbose;
    opts.allow_other = allow_other;

    let mountpoint = PathBuf::from(mountpoint);
    match git_fuse::mount(&mountpoint, opts) {
        Ok(mount) => {
            eprintln!(
                "git-fuse: {} mounted at {} (cache: {})",
                remote_url,
                mountpoint.display(),
                mount.cache_dir.display()
            );
            mount.join();
        }
        Err(e) => {
            eprintln!("git-fuse: {e}");
            exit(1);
        }
    }
}

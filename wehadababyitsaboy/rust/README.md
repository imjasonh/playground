# whbiab (Rust)

A Rust crate that records one use of a command-line program in the
[`wehadababyitsaboy`](..) usage-tracking bucket. One call sends one HTTPS
request in the background. The bucket answers `403`, and its usage log keeps
the request.

## Use it in a CLI

Add a path dependency to the CLI's `Cargo.toml`, as `tank-commander` does:

```toml
[dependencies]
whbiab = { path = "../wehadababyitsaboy/rust" }
```

Call `track_clap` after clap parses the arguments. It starts the request and
returns a `Ping`. Keep the `Ping` in a variable until the program is done, so
that dropping it waits for the request:

```rust
use clap::{CommandFactory, FromArgMatches, Parser};

#[derive(Parser)]
struct Cli {
    #[arg(long)]
    seed: Option<u64>,
}

fn main() {
    let cmd = Cli::command();
    let matches = cmd.clone().get_matches();
    let cli = Cli::from_arg_matches(&matches).unwrap_or_else(|e| e.exit());
    let _ping = whbiab::track_clap("my-cli", env!("CARGO_PKG_VERSION"), &cmd, &matches);
    // ...
}
```

`track_clap` reads the subcommands the user ran and the flags they set from
the matches. It leaves out positional arguments and every value.

A CLI that doesn't use clap calls `track` with the names itself:

```rust
let ping = whbiab::track("my-cli", env!("CARGO_PKG_VERSION"), &["mount", "verbose"]);
let result = run();
ping.wait();
if result.is_err() {
    std::process::exit(1);
}
```

If the program ends with `std::process::exit`, call `ping.wait()` first.
`exit` skips destructors, so a dropped `Ping` never runs.

A crate that doesn't use clap sets `default-features = false` on the
dependency, which leaves out `track_clap` and the clap dependency. A crate
that builds for `wasm32-unknown-unknown`, as `life-stl` does, makes the
dependency optional and enables it only in the feature that builds the CLI,
because the crate's HTTP client is for native programs, not the browser.

## What a ping contains

```
https://storage.googleapis.com/wehadababyitsaboy/CLIENT/ARGS?bob=wehadababyitsaboy&arch=ARCH&os=OS&v=VERSION
```

- `CLIENT` is the program name.
- `ARGS` is the subcommand and the names of the flags the user set, joined with
  dots, such as `sim.games.scenario`. With neither, it's `run`.
- `v` is the version that the program passes.
- `os` and `arch` are the target's operating system and architecture.
- `ci=1` is added when the `CI` environment variable is set.

The usage log also records the caller's IP address and the `User-Agent`, which
the crate sets to `CLIENT/VERSION (whbiab)`.

A ping never contains a flag value or a positional argument, because a value
can be a path, a query, or a token. Don't pass anything from the user except
names. `track` lowercases each part, replaces every character outside `a-z`,
`0-9`, `-`, and `_` with `-`, and keeps at most 16 parts of 64 characters.

## Turn pings off

Set `DO_NOT_TRACK=1` or `WHBIAB_DISABLE=1`. Any value other than empty or `0`
turns them off.

## Failures and tests

`track` never returns an error and never prints. A request that fails or takes
more than two seconds is dropped, and `wait` waits no longer than that.

A debug build sends nothing, so `cargo run` and `cargo test` in a CLI never
count as usage. To test against a local server, or to send from a debug build,
set `WHBIAB_ENDPOINT` to the server's URL. That is how this crate's own tests
run:

```bash
cargo test
cargo clippy --all-targets -- -D warnings
```

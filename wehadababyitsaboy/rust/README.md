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

The crate works with CLIs built on [clap](https://docs.rs/clap). Parse the
arguments with `whbiab::parse` in place of `Cli::parse()`. It returns the
parsed value and a `Ping` for the request it started. Keep the `Ping` in a
variable until the program is done, so that dropping it waits for the request:

```rust
use clap::Parser;

#[derive(Parser)]
#[command(name = "my-cli")]
struct Cli {
    #[arg(long)]
    seed: Option<u64>,
}

fn main() {
    let (cli, _ping) = whbiab::parse::<Cli>(env!("CARGO_PKG_VERSION"));
    // ...
}
```

`CLIENT` is the clap command's name. `parse` reads the subcommands the user ran
and the flags they set from clap's matches, and leaves out positional
arguments and every value. Like `Cli::parse()`, it exits for `--help`,
`--version`, and arguments that don't parse, and it sends nothing then.

If the program ends with `std::process::exit`, call `ping.wait()` first.
`exit` skips destructors, so a dropped `Ping` never runs. `git-fuse` does
this.

A crate that builds for `wasm32-unknown-unknown`, as `life-stl` does, makes the
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
names. The crate lowercases each part, replaces every character outside `a-z`,
`0-9`, `-`, and `_` with `-`, and keeps at most 16 parts of 64 characters.

## Turn pings off

Set `DO_NOT_TRACK=1` or `WHBIAB_DISABLE=1`. Any value other than empty, `0`,
or `false` turns them off.

## Failures and tests

A ping never fails the program and never prints. A request that fails or takes
more than two seconds is dropped, and `wait` waits no longer than that.

A debug build sends nothing, so `cargo run` and `cargo test` in a CLI never
count as usage. To test against a local server, or to send from a debug build,
set `WHBIAB_ENDPOINT` to the server's URL. That is how this crate's own tests
run:

```bash
cargo test
cargo clippy --all-targets -- -D warnings
```

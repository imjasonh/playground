//! memo runs a command, records what it read, and replays its output until
//! those inputs change.

#[cfg(not(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
compile_error!(
    "memo traces system calls with seccomp, so it builds only for Linux on x86_64 or aarch64"
);

mod cache;
mod capture;
mod cli;
mod fsstate;
mod http;
mod key;
mod net;
mod record;
mod trace;

fn main() {
    std::process::exit(cli::main(std::env::args_os().skip(1).collect()));
}

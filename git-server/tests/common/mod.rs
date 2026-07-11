//! Test-side alias for the crate's native harness. The implementation lives
//! in `git_server::testutil` so benchmarks (which cannot import `tests/`)
//! share the exact same server loop and git-runner instead of drifting
//! copies.

pub use git_server::testutil::{deterministic_noise, git, git_try, write_file, TestServer};

# Agent guide: git-server

A git smart-HTTP server for Cloudflare Workers, in Rust. Read
[`README.md`](README.md) for what it does and
[`docs/design.md`](docs/design.md) for the architecture. Repo-wide rules
(Rust apps are isolated crates, CI behavior, PR conventions) live in the
root [`AGENTS.md`](../AGENTS.md); this file adds the rules specific to this
crate.

## Hard rules

- **`docs/api.md` must stay accurate.** Any change that adds, removes, or
  alters an API method — a git smart-HTTP route or a `/api/…` endpoint —
  must update `docs/api.md` in the same change.
- **Never buffer whole packs.** Fetch responses stream via `PackEmitter`;
  push bodies stream into R2 via `PackIngest`. `tests/memory.rs` enforces a
  transient-heap budget; treat a failure there as a real production bug
  (the Workers isolate has a hard 128 MiB limit).
- **Everything except `worker_entry.rs` must build and test natively.**
  Business logic goes in the transport-agnostic modules so `cargo test`
  exercises the same code the Worker runs. `worker_entry.rs` is thin glue —
  it gets no automated execution in CI (only `scripts/e2e.sh`, run
  manually), so logic hiding there is logic without tests.

## Verify before you're done

```bash
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
cargo clippy --locked --target wasm32-unknown-unknown -- -D warnings   # Worker glue
```

CI runs all of the above (see root `AGENTS.md` → Testing). Integration
tests need `git` on PATH.

## Deslop

This codebase was built fast, and a code-quality audit found recurring
patterns of "slop" — code that works but decays: dead compat shims, stale
comments, drifting copies. These rules exist so the same slop doesn't grow
back. Bugbot and reviewers should flag violations.

### No dead or vestigial API

- **When changing a function's signature, update every caller.** Do not
  leave the old signature behind as a wrapper (`foo` delegating to
  `foo_with_options`) — this crate has no external consumers, so there is
  no compatibility to preserve. Rename, fix the call sites, delete the old
  name.
- **Before adding a `pub` item, have a caller for it.** Speculative API
  ("might need this later") gets deleted by the next audit. Before
  committing, `rg` the symbol: if its only uses are its own definition and
  its own tests, it goes.
- **Default to `pub(crate)`** unless integration tests or benches (which
  link the crate externally) genuinely need the item.
- **Don't silence dead-code warnings.** `#[allow(dead_code)]` is almost
  always wrong here: either the item is used (drop the attribute) or it
  isn't (drop the item). The two stale allows this rule replaced both
  suppressed nothing.

### Comments describe the present, not the journey

- **No bug-chase narratives.** "Was briefly halved while chasing a
  suspected memory bug; the real failure was CPU…" belongs in the commit
  message or PR description, not in the code. State the current rationale
  for the current value, and cite the test that enforces it if one exists.
- **A comment that repeats a number defined elsewhere will rot.** Cite the
  constant by name (`CONTENT_CACHE_BUDGET`) instead of inlining its value
  in prose. `docs/design.md` carried cache sizes that were 2× stale for
  exactly this reason.
- **Module docs are part of the feature.** Adding a protocol capability
  (shallow, filter, …) means extending the module doc that lists supported
  features, plus `README.md`, `docs/api.md`, and `docs/design.md`. Grep
  the docs for "not supported" claims your change invalidates.
- **Tests' comments must match their assertions.** If you change what a
  test asserts, re-read its doc comment.

### One implementation per concept

Extend the existing helper instead of pasting a variant. Current single
homes, so you know where to look before writing a new one:

| Concept | Single home |
|---|---|
| zlib inflate (one-shot) | `pack::write::{inflate, inflate_unchecked}` |
| zlib deflate | `pack::write::deflate` |
| Byte-budgeted object cache | `cache::ByteBudgetCache` |
| Pack entry emission | `PackWriter` streaming API (`begin_* / append_payload / end_entry`); one-shot `add_*` wrap it |
| Pack-index sorting | `PackIndex::new` (nowhere else) |
| Tree-mode check | `object::is_tree_mode` / `TreeEntry::is_tree` |
| Cost model ($/op) | `metrics::cost` |
| Native HTTP harness, git runner, noise generator, pack-install fixture | `testutil` (shared by `tests/` **and** `benches/` — benches cannot import `tests/common`, so never copy the harness into a bench) |
| Delta-chain depth limit | `pack::MAX_DELTA_CHAIN` |

If you must duplicate something for a real reason (e.g. the scanner's
*incremental* inflate cannot use the one-shot helper), say why in a comment
at the copy.

### Name the number

A literal that appears in two places, or whose meaning isn't obvious at the
use site (`91`, `0x10000`, `10_000`), becomes a named constant with a
one-line rationale — next to the code that defines the format if it's a
format constant (`GSFL_RECORD_FIXED_BYTES` lives beside `to_bytes`).

### Error text is API

Use the established vocabulary — `object {oid} not found`, `bad <field>`,
`unsupported <thing>` — rather than inventing synonyms ("vanished",
"missing", "gone") for the same failure mode. Tests and log greps depend on
these strings.

### Every reachable error path gets a test

If a client can trigger a response — an in-band `ERR` pkt, a report-status
`ng`, a 4xx/5xx — there should be a test that does trigger it. The audit
found `error_response` itself had zero coverage: every protocol rejection
was dead-in-tests. When adding a fetch/push option, test the rejection
branch in the same PR as the feature (see `fetch_error_responses` in
`tests/integration.rs` for the pattern — raw v2 bodies via
`TestServer::post_with_body`, no git client needed).

Checking coverage locally (`cargo llvm-cov` needs rustc ≥ its own MSRV;
current `cargo-llvm-cov` works with this crate's pinned 1.88):

```bash
rustup component add llvm-tools
cargo install cargo-llvm-cov --locked
cargo llvm-cov --no-report && cargo llvm-cov report --show-missing-lines
```

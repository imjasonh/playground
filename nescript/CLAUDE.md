# CLAUDE.md

Guidance for Claude Code (and any other AI agents) working in this repo.
Keep it short and practical — it's here so the next agent doesn't have to
re-derive the project conventions from scratch.

---

## Project shape

- **NEScript** is a Rust-based compiler that turns `.ne` source files into
  iNES ROMs. Single binary, no external assemblers, no external linkers.
- `src/` is a flat module layout: each compiler phase is its own directory
  with `mod.rs` + `tests.rs`. See `docs/architecture.md` for the phase
  pipeline.
- Examples live in `examples/*.ne`. Every example is expected to compile
  cleanly and has a pinned emulator golden — see below.
- **`examples/*.nes` is committed.** The compiler is deterministic
  (same source → byte-identical ROM), so the ROMs travel with the
  repo. If you edit any `.ne` file you **must** rebuild its `.nes`
  in the same commit — CI's `examples` job rebuilds each ROM into a
  tmp path and fails if the committed version differs, pointing at
  the exact `cargo run -- build examples/<name>.ne` to run. The
  pre-commit hook under `scripts/pre-commit` catches this locally.
- **`docs/platformer.gif`, `docs/war.gif`, and `docs/pong.gif` are
  committed** and embedded in the top-level README as the project
  demos. `gifenc` + `jsnes` are deterministic, so each gif's bytes
  are a function of the compiler, the runtime, the harness, and
  the underlying `.ne` source(s). Any change to those that affects
  the first ~6 seconds of observable gameplay must be followed by
  regenerating the affected gif:

  ```bash
  node tests/emulator/record_gif.mjs platformer 360 2 docs/platformer.gif
  node tests/emulator/record_gif.mjs war        360 2 docs/war.gif        4
  node tests/emulator/record_gif.mjs pong       360 2 docs/pong.gif       4
  ```

  (The trailing `4` on the war and pong commands is the
  warmup-frames override — both open on a title menu that we want
  as the gif thumbnail, so we don't skip past it the way the
  platformer recording does.) Commit the regenerated gif in the
  same change. CI's `emulator` job renders fresh gifs and fails if
  any committed copy doesn't byte-match. The pre-commit hook
  rebuilds whichever gif is affected when `platformer.ne`,
  `platformer.nes`, any file under `examples/war/`, `war.ne`,
  `war.nes`, any file under `examples/pong/`, `pong.ne`,
  `pong.nes`, `record_gif.mjs`, or `harness.html` is staged (and
  `tests/emulator/node_modules` is installed).
- `docs/future-work.md` lists the remaining gaps. If you implement
  something from that file, update the doc in the same PR.

## Running the basics

```bash
cargo build --release              # build the compiler
cargo test --all-targets           # all Rust tests — MUST include --all-targets
cargo fmt                          # mandatory before committing
cargo clippy --all-targets -- -D warnings   # mandatory; fix or #[allow]
./target/release/nescript build examples/hello_sprite.ne   # build one ROM
```

**Always pass `--all-targets` to `cargo test`.** CI runs `cargo test
--all-targets`, which additionally compiles and smoke-runs the `compile`
benchmark under `benches/compile.rs`. A plain `cargo test` skips that,
so a bench that doesn't compile will pass locally and red-flag CI —
this exact failure mode bit us once already (commit `889074a`).

The repo ships a pre-commit hook at `scripts/pre-commit` that runs
`cargo fmt --check`, `cargo clippy --all-targets -- -D warnings`,
`cargo test --all-targets`, and the committed-ROM reproducibility diff.
Install it once per worktree with:

```bash
cp scripts/pre-commit .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit
```

Do this before your first commit in a new worktree. The hook catches
stale ROMs, stale platformer gif, and divergent bench/compile pipelines
before they hit CI.

Compile every example at once:

```bash
for f in examples/*.ne; do cargo run --release -- build "$f"; done
```

## The jsnes emulator harness

This is the most important piece of project-specific tooling. Every `.ne`
example has a **pixel-exact PNG golden** and a **sample-exact audio hash**
committed under `tests/emulator/goldens/`. Any compiler change that alters
observable behaviour — codegen, optimizer, runtime, linker, asset pipeline
— will flip at least one golden, and CI will fail loudly with a visible
diff. Do not skip or weaken this check.

### Layout

```
tests/emulator/
  harness.html          # thin wrapper around jsnes; exposes window.nesHarness
                        # with loadRomBase64, runFrames, rawPixelsBase64,
                        # audioHash, audioWavBase64
  run_examples.mjs      # puppeteer-driven runner (headless Chrome)
  package.json          # depends on jsnes, pngjs, puppeteer
  goldens/
    <name>.png          # 256×240 RGBA framebuffer at frame 180 (~3s at 60fps)
    <name>.audio.hash   # one line: "<fnv1a-hex> <sample-count>"
  actual/               # gitignored; written on every run for diff artifacts
```

### Running it locally

The harness is **separate** from `cargo test`. You have to run it by hand:

```bash
# 1. Rebuild every example with the current compiler. The harness
#    reads whatever sits under examples/*.nes — if you want to test
#    your working copy you have to rebuild them first.
cargo build --release
for f in examples/*.ne; do ./target/release/nescript build "$f"; done

# 2. Install node deps (once per worktree; node_modules/ is gitignored).
cd tests/emulator
npm install          # or `npm ci` in CI

# 3. Verify every ROM still matches its golden.
node run_examples.mjs
# → "22/22 ROMs match their goldens" on success
# → FAIL / MISS lines + `actual/<name>.png`, `actual/<name>.diff.png`,
#   `actual/<name>.wav` written for any ROM that mismatched
```

The harness always runs against whatever sits in `examples/*.nes`,
so iterating on the compiler means rebuilding the example first.
CI's `emulator` job does this too — it builds the compiler, compiles
every `.ne` into the workspace (overwriting the committed ROMs,
which are ephemeral in the CI checkout), and then runs the harness.
The committed ROMs are a PR-review convenience and a "did this
change affect codegen" tripwire via the `examples` job's
reproducibility diff; they are **not** what the emulator job tests.

### Updating goldens

If a change is supposed to flip goldens (you added a new example, changed
a rendering path, fixed a bug that was baked into the old output), update
them with:

```bash
cd tests/emulator
UPDATE_GOLDENS=1 node run_examples.mjs     # rewrites every mismatched golden
# or
node run_examples.mjs --update-goldens
```

Then `git diff tests/emulator/goldens/` the result, eyeball each change,
and include the updated PNG+hash files in the same commit as the code
change. Goldens are the contract; the commit message should explain why
each diff is legitimate. **Never** `UPDATE_GOLDENS=1` just to silence a
failing CI — that defeats the entire purpose of the harness.

### Adding a new example

1. Write `examples/<name>.ne`.
2. Build it with the release compiler so a `.nes` file lands next to it.
3. Run `UPDATE_GOLDENS=1 node run_examples.mjs` to generate
   `goldens/<name>.png` and `goldens/<name>.audio.hash`. Both files must
   be committed — the runner treats missing goldens as a hard failure.
4. Verify visually that the generated PNG is what you actually intended
   (open it; you can use Read on the PNG file to have Claude display it).
5. Add the example to the tables in `README.md` and `examples/README.md`.

### What the harness tests (and doesn't)

- **Tests**: final rendered framebuffer at frame 180, full audio sample
  stream over the same window. Catches codegen miscompiles, runtime
  bugs, linker layout changes, PPU timing regressions, APU regressions,
  asset pipeline bugs — essentially anything that affects the observable
  behaviour of a whole program.
- **Does not test**: input handling (no buttons pressed during the run),
  anything past frame 180 (~3 seconds), state transitions that require
  user input. Examples that need input to look non-trivial should
  structure themselves so a good demo happens on autopilot — e.g. a
  frame counter that drives the interesting state (`examples/palette_and_background.ne`
  is a working pattern).

### CI integration

The `emulator` job in `.github/workflows/ci.yml` installs Chrome deps,
builds all examples, then runs the harness. On failure it uploads the
`actual/` directory and `report.json` as an artifact named `emulator-diff`
so reviewers can download and inspect the pixel diffs without cloning the
repo. The CI job does **not** pass `UPDATE_GOLDENS`; if it flips, the
change needs a manual update + review.

## Conventions worth knowing

- Every `src/**/mod.rs` has a co-located `tests.rs`. Add unit tests
  there, not in a separate file.
- Big cross-phase tests go in `tests/integration_test.rs`. Use the
  `compile` / `compile_banked` helpers at the top of that file instead
  of re-building the pipeline by hand.
- Error codes live in `src/errors/diagnostic.rs`. Don't add a new code
  without emitting it from somewhere — clippy will catch unused variants,
  but past agents have also let them sit as dead code.
- Zero page is tight. `$00-$0F` is reserved for the runtime (frame
  flag, input, OAM cursor, sfx/music pointers). `$11-$17` is reserved
  for PPU palette/background updates **when the program declares them**
  (the analyzer bumps the user ZP start from `$10` to `$18` in that
  case — programs without palette/bg keep the old `$10` layout to
  preserve their goldens). User vars go at `$10+` or `$18+`; IR temps
  land at `$80+`.
- State-local variables (declared at `state Foo { var x }`) are
  automatically **overlaid** across states. The analyzer snapshots
  the ZP/RAM cursors after the globals are laid out, rewinds to the
  snapshot before each state's locals, and advances to the running
  max at the end. Because `ZP_CURRENT_STATE` makes at most one state
  active at runtime, two states' locals can share the same bytes —
  the IR lowerer re-emits each state's declared initializers at the
  top of its `on_enter` handler (synthesizing one if needed) so a
  freshly entered state doesn't inherit the previous state's writes.
  `--memory-map` annotates each allocation with its owning state
  (`[@Title]`, `[@Playing]`, ...) so the overlay shows up in the
  report.
- `docs/future-work.md` is the authoritative roadmap. If you finish an
  item, delete its section; if you add a new gap, write one.

## New-feature PR checklist (don't ship silent drops)

PR #31 shipped a year-old state-local bug where the analyzer
allocated ZP slots for `state Foo { var x }` but the IR codegen
silently emitted zero bytes for every `LoadVar`/`StoreVar` on them.
The bug survived because pixel/audio goldens captured the broken
behaviour as ground truth and no test asserted a write-wait-read
round-trip. Several other features (uninitialized struct-field
writes, `on exit` handlers, `slow` placement, state-local array
initializers) had the same shape when we audited. To avoid
repeating the pattern, every new language-feature PR must include:

1. **An example program** under `examples/` that exercises the
   feature on a path the emulator harness can observe at frame
   180. If the feature doesn't produce visible output on
   autopilot, rig a frame counter to drive it (see
   `examples/palette_and_background.ne` for the pattern).
2. **A runtime behaviour assertion**, not just a shape or
   byte-level assertion. Integration tests that only
   `rom::validate_ines(&rom)` the output are ROM-*is-valid*
   tests, not *feature-works* tests — they pass against a
   compiler that silently drops the feature. Either add a
   byte-level assertion that the expected instruction sequence
   appears (e.g. `LDA #$7B / STA <addr>` for a known-value
   write, as
   `uninitialized_struct_field_store_emits_sta_to_allocated_address`
   does), or — better — a round-trip test that compiles
   `write(42) → wait_frame → assert(read == 42)` and fails
   against a silently-dropping codegen.
3. **A negative test** that gives the analyzer a program using
   the feature invalidly and asserts the right error code fires.
   Without this, a future refactor that stops emitting the
   diagnostic lets the silent-drop shape back in.

Address-map lookups in the codegen are a specific trap: the
pattern `if let Some(&addr) = self.<some_map>.get(var) { ... }`
with no `else` branch is how PR #31 shipped. If an IR op
references a `VarId` / state name / function name, treat a map
miss as a **compiler bug** and panic — use
`IrCodeGen::var_addr(var)` or an explicit `.unwrap_or_else(||
panic!(...))`. A silent zero-byte emit is worse than a crash.

## Things to avoid

- **Don't add backwards-compat shims.** The repo is pre-1.0; breaking
  changes are fine if they improve the code. Delete dead code outright
  rather than `#[allow(dead_code)]`-ing it.
- **Don't skip `cargo fmt` / `cargo clippy`.** CI runs both and they
  are cheap.
- **Don't `UPDATE_GOLDENS=1` without reading the diff.** If you can't
  explain why a golden flipped, the change is probably wrong.
- **Don't commit `tests/emulator/actual/` or `tests/emulator/node_modules/`.**
  Both are gitignored, but it's worth double-checking before a commit
  that touches the emulator directory.

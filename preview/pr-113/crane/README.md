# Yard Crane

Operate a tower crane in a circular construction yard. Slew the jib, run the
trolley, hoist the hook, and ferry three color-matched crates to their
destinations — slowly, like a real heavy lift. The clock runs until the yard
is clear.

This is a **Godot 4** game exported to a single-threaded WebAssembly build so it
runs on GitHub Pages without `SharedArrayBuffer` / COOP+COEP headers.

## Play

- **Slew** — `A` / `D` or `←` / `→` (on-screen: Slew buttons)
- **Trolley** — `W` / `S` or `↑` / `↓` (in / out along the boom)
- **Hoist** — `Q` / `E` (or `R` / `F`) raise / lower the hook
- **Grab / release** — `Space` or the **GRAB** button

Three crates (coral, blue, amber). Each pickup sits opposite its glowing drop
pad across the yard — never side by side. Deliver all three; crates stay put
once placed. Beat your time.

The hook swings with crane motion — accelerate gently, wait for the load to
settle, then set it down.

## Run locally

Serve the exported files (opening `index.html` as a file:// URL will not work):

```bash
npm start
```

Then open <http://localhost:3000>.

## Develop (Godot editor)

1. Install [Godot 4.4.1+](https://godotengine.org/download) (same minor as
   `src/project.godot`).
2. Install the matching **export templates**.
3. Open `src/` as the project.
4. Re-export for the web:

```bash
npm run export
# or: GODOT_BIN=/path/to/godot bash scripts/export.sh
```

The export writes `index.html`, `index.js`, `index.wasm`, and `index.pck` into
this directory (the browser app root). Deploy copies that directory as-is — no
CI Godot build step — so **commit the export artifacts** when gameplay changes.

`src/export_presets.cfg` keeps `variant/thread_support=false` on purpose for
Pages compatibility.

## Test

```bash
npm test
```

Smoke-checks that the web export artifacts exist, look single-threaded, and that
the Godot source/preset stay wired for a nothreads Web build.

#!/usr/bin/env bash
# Re-export the Godot project to web (single-threaded, GitHub Pages friendly).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/src"
OUT="$ROOT/index.html"

GODOT_BIN="${GODOT_BIN:-}"
if [[ -z "$GODOT_BIN" ]]; then
  for candidate in \
    godot \
    godot4 \
    /tmp/godot-bin/Godot_v4.4.1-stable_linux.x86_64 \
    "$HOME/bin/godot"
  do
    if command -v "$candidate" >/dev/null 2>&1; then
      GODOT_BIN="$(command -v "$candidate")"
      break
    elif [[ -x "$candidate" ]]; then
      GODOT_BIN="$candidate"
      break
    fi
  done
fi

if [[ -z "${GODOT_BIN}" ]]; then
  echo "Godot 4.4.1+ not found. Set GODOT_BIN to the engine binary." >&2
  exit 1
fi

echo "Using Godot: $GODOT_BIN ($("$GODOT_BIN" --version))"
"$GODOT_BIN" --headless --path "$SRC" --export-release "Web" "$OUT"
echo "Exported → $ROOT/index.html (+ .wasm .pck .js)"

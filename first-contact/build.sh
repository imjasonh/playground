#!/usr/bin/env bash
# Build one card bundle from its generator and render frame 0.
#
# Usage: ./build.sh <robot|astronaut|alien> [out.klad]
#
# klad is source-available and not on this repo's CI, so you build it yourself
# (https://github.com/klad-app/klad) and point this script at the binary with
# KLAD=/path/to/klad, or put `klad` on your PATH. KLAD_FONTS can point at the
# repo's fonts/ folder when the binary can't find its own.
# SKETCH=1 stops after the first pass and renders the lit underpaintings
# without any brushwork, which is quicker still.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
name="${1:?give a card: robot, astronaut, or alien}"
out="${2:-$here/$name.klad}"
python="${PYTHON:-python3}"

klad="${KLAD:-$(command -v klad || true)}"
if [ -z "$klad" ]; then
  echo "klad not found: build it from https://github.com/klad-app/klad and set KLAD=/path/to/klad, or put klad on your PATH" >&2
  exit 1
fi

if [ ! -f "$here/$name.py" ]; then
  echo "no generator $here/$name.py (expected robot, astronaut, or alien)" >&2
  exit 1
fi

if [ -e "$out" ] && [ "${FORCE:-0}" != 1 ]; then
  echo "$out exists and may hold editor changes; pass another path or FORCE=1 to rebuild it" >&2
  exit 1
fi

rm -rf "$out"
"$klad" new "$out" --width 1024 --height 1280 --layers 0 >/dev/null

# The generator prints its ops in batches. The first lays out the lit
# underpaintings; each paint-over needs a batch of its own, because it reads
# the drawing as it stands; the last one rigs the pieces and keys the loop.
passes="$("$python" "$here/$name.py" --passes)"
if [ "${SKETCH:-0}" = 1 ]; then
  export SKETCH
  passes=1
fi
for ((i = 0; i < passes; i++)); do
  "$python" "$here/$name.py" --pass "$i" | "$klad" apply "$out" >/dev/null
done

"$klad" render "$out" -o "${out%.klad}.png" >/dev/null
echo "built $out and ${out%.klad}.png"

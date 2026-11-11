#!/usr/bin/env bash
# Build all three cards and compose them into one wide triptych bundle.
#
# Usage: ./triptych.sh
#
# Needs the klad binary (see build.sh for how to get it): set KLAD=/path/to/klad
# or put `klad` on your PATH, and KLAD_FONTS if the binary can't find its fonts.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"

klad="${KLAD:-$(command -v klad || true)}"
if [ -z "$klad" ]; then
  echo "klad not found: build it from https://github.com/klad-app/klad and set KLAD=/path/to/klad, or put klad on your PATH" >&2
  exit 1
fi

# One panel per archetype, left to right, in story order.
cards=(robot astronaut alien)
for name in "${cards[@]}"; do
  FORCE=1 "$here/build.sh" "$name" >/dev/null
done

# A 3248x1408 canvas holds three 1024x1280 panels with a 40px gutter and a 48px
# margin, centred vertically ((1408-1280)/2 = 64).
out="$here/triptych.klad"
rm -rf "$out"
"$klad" new "$out" --width 3248 --height 1408 --layers 0 >/dev/null

bg="$("$klad" add "$out" layer vector name=bg --json | "${PYTHON:-python3}" -c 'import json,sys; print(json.load(sys.stdin)["added"][0])')"
"$klad" add "$out" rect --in "$bg" x=0 y=0 w=3248 h=1408 \
  'fill={"linear":{"from":[0,0],"to":[0,1408],"stops":[[0,"#070613"],[0.5,"#140d2c"],[1,"#070613"]]}}' >/dev/null

for name in "${cards[@]}"; do
  "$klad" add "$out" layer image src="$here/$name.png" >/dev/null
done

# Place each panel by its layer name (the image layer takes the file's name).
"$klad" ls "$out" --json | "${PYTHON:-python3}" -c '
import json
import sys

x = {"robot": 48, "astronaut": 1112, "alien": 2176}
doc = json.load(sys.stdin)
for layer in doc["layers"]:
    if layer["name"] in x and layer.get("nodes"):
        node = layer["nodes"][0]["id"]
        print(json.dumps({"op": "set", "id": node, "x": x[layer["name"]], "y": 64}))
' | "$klad" apply "$out" >/dev/null

"$klad" render "$out" -o "$here/triptych.png"
echo "built $out and $here/triptych.png"

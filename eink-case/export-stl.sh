#!/usr/bin/env bash
# Export the two printable parts as binary STLs.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/stl}"
mkdir -p "$OUT"

echo "Exporting front shell ..."
openscad -o "$OUT/front.stl" \
  -D 'part="front"' \
  "$ROOT/case.scad"

echo "Exporting back lid ..."
openscad -o "$OUT/back.stl" \
  -D 'part="back"' \
  "$ROOT/case.scad"

# Also write a small dims note from the OpenSCAD echoes
openscad -o /dev/null -D 'part="front"' "$ROOT/case.scad" 2>"$OUT/dimensions.txt" || true
grep -E 'CLOSED|Printable|Lid screws|Board screws|Bay depth|Panel pocket' "$OUT/dimensions.txt" || true

ls -la "$OUT"
echo "Done."

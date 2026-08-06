#!/usr/bin/env bash
# Multi-angle previews via the vendored OpenSCAD skill tools.
# Usage: bash render.sh [output_root]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/previews}"
TOOLS="$ROOT/tools"

mkdir -p "$OUT"

echo "== validate =="
"$TOOLS/validate.sh" "$ROOT/case.scad"

echo ""
echo "== assembled (with ghost components) =="
"$TOOLS/multi-preview.sh" "$ROOT/case.scad" "$OUT/assembled" \
  -D 'part="assembled"' -D 'show_components=true'

echo ""
echo "== front shell =="
"$TOOLS/multi-preview.sh" "$ROOT/case.scad" "$OUT/front" \
  -D 'part="front"'

echo ""
echo "== back lid =="
"$TOOLS/multi-preview.sh" "$ROOT/case.scad" "$OUT/back" \
  -D 'part="back"'

echo ""
echo "== parameters =="
"$TOOLS/extract-params.sh" "$ROOT/case.scad" | head -60

echo ""
echo "Previews under $OUT — visually inspect every PNG before shipping."

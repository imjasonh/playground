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
echo "== assembled =="
"$TOOLS/multi-preview.sh" "$ROOT/case.scad" "$OUT/assembled" \
  -D 'part="assembled"' -D 'show_components=true'

for p in shell cap key; do
  echo ""
  echo "== $p (print orientation) =="
  "$TOOLS/multi-preview.sh" "$ROOT/case.scad" "$OUT/$p" \
    -D "part=\"$p\""
done

echo ""
echo "== parameters =="
"$TOOLS/extract-params.sh" "$ROOT/case.scad"

echo ""
echo "Previews under $OUT — inspect every PNG; see LEARNINGS.md + tools/fdm-design-rules.md"

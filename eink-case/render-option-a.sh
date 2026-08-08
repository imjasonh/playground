#!/usr/bin/env bash
# Render the Option A concept from multiple angles.
# Usage: bash render-option-a.sh [output_root]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/previews/option-a}"
TOOLS="$ROOT/tools"
MODEL="$ROOT/option-a.scad"

mkdir -p "$OUT"

echo "== validate Option A =="
"$TOOLS/validate.sh" "$MODEL"

echo ""
echo "== assembled shape =="
"$TOOLS/multi-preview.sh" "$MODEL" "$OUT/assembled" \
  -D 'part="assembled"' -D 'show_components=false'

echo ""
echo "== exploded hardware =="
"$TOOLS/multi-preview.sh" "$MODEL" "$OUT/exploded" \
  -D 'part="assembled"' -D 'show_components=true' -D 'explode=18'

for p in shell cap pod_cover key; do
  echo ""
  echo "== $p (print orientation) =="
  "$TOOLS/multi-preview.sh" "$MODEL" "$OUT/$p" \
    -D "part=\"$p\""
done

echo ""
echo "Option A previews: $OUT"

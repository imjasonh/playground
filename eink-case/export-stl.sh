#!/usr/bin/env bash
# Export the two printable parts using the vendored OpenSCAD skill tools.
# Usage: bash export-stl.sh [output_dir]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/stl}"
TOOLS="$ROOT/tools"

mkdir -p "$OUT"

echo "== validate =="
"$TOOLS/validate.sh" "$ROOT/case.scad"

echo ""
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/front.stl" -D 'part="front"'
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/back.stl"  -D 'part="back"'

# Capture dimension echoes next to the STLs
"$TOOLS/validate.sh" "$ROOT/case.scad" 2>/dev/null \
  | sed -n 's/^ECHO: "\(.*\)"/\1/p' > "$OUT/dimensions.txt" || true
# validate.sh already prints echoes without ECHO: prefix after "Echo output:"
"$TOOLS/validate.sh" "$ROOT/case.scad" > "$OUT/validate.log" 2>&1 || true
python3 - <<PY
from pathlib import Path
log = Path("$OUT/validate.log").read_text()
lines = []
capture = False
for line in log.splitlines():
    if line.startswith("Echo output:"):
        capture = True
        continue
    if capture:
        if line.startswith("=") and lines:
            break
        if line.strip():
            lines.append(line)
Path("$OUT/dimensions.txt").write_text("\n".join(lines) + ("\n" if lines else ""))
print("\n".join(lines))
PY

ls -la "$OUT"
echo "Done. Remember: visual multi-preview validation before merging geometry changes."

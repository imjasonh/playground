#!/usr/bin/env bash
# Export the printable parts using the vendored OpenSCAD skill tools.
# Usage: bash export-stl.sh [output_dir]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/stl}"
TOOLS="$ROOT/tools"

mkdir -p "$OUT"

echo "== validate =="
"$TOOLS/validate.sh" "$ROOT/case.scad" | tee "$OUT/validate.log"

echo ""
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/shell.stl" -D 'part="shell"'
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/cap.stl"   -D 'part="cap"'

# Remove legacy 3-piece STLs if present
rm -f "$OUT/bezel.stl" "$OUT/tray.stl" "$OUT/back.stl" "$OUT/front.stl"

python3 - <<PY
from pathlib import Path
log = Path("$OUT/validate.log").read_text()
lines = []
for line in log.splitlines():
    if line.startswith('ECHO: "'):
        lines.append(line[len('ECHO: "'):-1])
Path("$OUT/dimensions.txt").write_text("\n".join(lines) + ("\n" if lines else ""))
if lines:
    print("\n".join(lines))
PY

ls -la "$OUT"
echo "Done. Visually inspect previews (bash render.sh) before merging geometry changes."

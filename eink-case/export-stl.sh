#!/usr/bin/env bash
# Export the three printable parts using the vendored OpenSCAD skill tools.
# Usage: bash export-stl.sh [output_dir]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/stl}"
TOOLS="$ROOT/tools"

mkdir -p "$OUT"

echo "== validate =="
"$TOOLS/validate.sh" "$ROOT/case.scad" | tee "$OUT/validate.log"

echo ""
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/bezel.stl" -D 'part="bezel"'
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/tray.stl"  -D 'part="tray"'
"$TOOLS/export-stl.sh" "$ROOT/case.scad" "$OUT/back.stl"  -D 'part="back"'

# Remove legacy combined front if present
rm -f "$OUT/front.stl"

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

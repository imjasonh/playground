#!/usr/bin/env bash
# Export the separate Option A direct-connect backpack concept.
# Usage: bash export-option-a.sh [output_dir]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/stl}"
TOOLS="$ROOT/tools"
MODEL="$ROOT/option-a.scad"

mkdir -p "$OUT"

echo "== validate Option A =="
"$TOOLS/validate.sh" "$MODEL" | tee "$OUT/option-a-validate.log"

echo ""
"$TOOLS/export-stl.sh" "$MODEL" "$OUT/option-a-shell.stl" \
  -D 'part="shell"'
"$TOOLS/export-stl.sh" "$MODEL" "$OUT/option-a-cap.stl" \
  -D 'part="cap"'
"$TOOLS/export-stl.sh" "$MODEL" "$OUT/option-a-pod-cover.stl" \
  -D 'part="pod_cover"'
"$TOOLS/export-stl.sh" "$MODEL" "$OUT/option-a-key.stl" \
  -D 'part="key"'

python3 - <<PY
from pathlib import Path
log = Path("$OUT/option-a-validate.log").read_text()
lines = []
for line in log.splitlines():
    if line.startswith('ECHO: "'):
        lines.append(line[len('ECHO: "'):-1])
Path("$OUT/option-a-dimensions.txt").write_text(
    "\n".join(lines) + ("\n" if lines else "")
)
if lines:
    print("\n".join(lines))
PY

ls -la "$OUT"/option-a-*
echo "Print: 1 shell, 1 cap, 1 pod cover, 2 identical keys."

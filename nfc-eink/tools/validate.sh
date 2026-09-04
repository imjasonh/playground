#!/usr/bin/env bash
# Schematic netlist check, PCB presence check, firmware host tests.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"

if ! command -v kicad-cli >/dev/null 2>&1; then
  echo "kicad-cli not found. Install KiCad 7 or later." >&2
  exit 2
fi

python3 tools/erc.py
python3 tools/pcb_check.py
make -C firmware test

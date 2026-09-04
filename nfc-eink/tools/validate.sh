#!/usr/bin/env bash
# Export a KiCad netlist and fail on unexpected unconnected pins.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"

if ! command -v kicad-cli >/dev/null 2>&1; then
  echo "kicad-cli not found. Install KiCad 7 or later." >&2
  exit 2
fi

python3 tools/erc.py

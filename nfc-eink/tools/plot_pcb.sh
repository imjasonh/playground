#!/usr/bin/env bash
# Plot copper layers and the board outline to SVG + PDF.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"

if ! command -v kicad-cli >/dev/null 2>&1; then
  echo "kicad-cli not found." >&2
  exit 2
fi

mkdir -p plots

kicad-cli pcb export svg --output plots/nfc-eink-front.svg --layers "F.Cu,F.SilkS,Edge.Cuts" --page-size-mode 2 --exclude-drawing-sheet nfc-eink.kicad_pcb
kicad-cli pcb export svg --output plots/nfc-eink-back.svg --layers "B.Cu,B.SilkS,Edge.Cuts" --mirror --page-size-mode 2 --exclude-drawing-sheet nfc-eink.kicad_pcb
kicad-cli pcb export svg --output plots/nfc-eink-back-silk.svg --layers "B.SilkS,Edge.Cuts" --page-size-mode 2 --exclude-drawing-sheet nfc-eink.kicad_pcb
kicad-cli pcb export svg --output plots/nfc-eink-layers.svg --layers "F.Cu,B.Cu,In1.Cu,In2.Cu,F.SilkS,B.SilkS,Edge.Cuts" --page-size-mode 2 --exclude-drawing-sheet nfc-eink.kicad_pcb
kicad-cli pcb export pdf --output plots/nfc-eink-pcb.pdf --layers "F.Cu,B.Cu,In1.Cu,In2.Cu,F.SilkS,B.SilkS,Edge.Cuts" nfc-eink.kicad_pcb

echo "wrote plots/"

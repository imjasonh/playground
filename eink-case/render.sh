#!/usr/bin/env bash
# Render preview PNGs of the e-ink case from useful angles.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$ROOT/renders}"
mkdir -p "$OUT"

IMG=1600,1200
SCAD="$ROOT/case.scad"

# OpenSCAD camera: tx,ty,tz, rotx,roty,rotz, dist
# With --autocenter --viewall, dist is ignored; rotations set the view.
# rotX=0 looks along -Z at the high-Z face (lid / back of device).
# rotX=180 looks at the display face (z=0).

render() {
  local name="$1"; shift
  echo "Rendering $name ..."
  openscad -o "$OUT/$name.png" \
    --imgsize="$IMG" \
    --colorscheme=Tomorrow \
    --preview \
    "$@" \
    "$SCAD" 2>/dev/null
}

# Display face (true front)
render 01-display-face \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,180,0,0,0 --autocenter --viewall

# Three-quarter from front
render 02-three-quarter-front \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,140,0,35,0 --autocenter --viewall

# Back / lid with USB notch
render 03-back-lid \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,40,0,25,0 --autocenter --viewall

# USB wall (left / -X)
render 04-usb-wall \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,70,0,-80,0 --autocenter --viewall

# FPC insertion edge (bottom / -Y)
render 05-fpc-edge \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,70,0,180,0 --autocenter --viewall

# Exploded assembly
render 06-exploded \
  -D 'part="assembled"' -D show_components=true -D explode=20 \
  --camera=0,0,0,125,0,40,0 --autocenter --viewall

# Front shell alone — looking into the bay (groove + window)
render 07-front-shell-interior \
  -D 'part="front"' \
  --camera=0,0,0,55,0,30,0 --autocenter --viewall

# Front shell — display face
render 08-front-shell-display \
  -D 'part="front"' \
  --camera=0,0,0,160,0,20,0 --autocenter --viewall

# Cross-section helper: assembled, components, viewed from side close up
render 09-side-sectionish \
  -D 'part="assembled"' -D show_components=true -D explode=0 \
  --camera=0,0,0,80,0,90,0 --autocenter --viewall

echo "Done → $OUT"
ls -la "$OUT"

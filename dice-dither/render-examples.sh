#!/usr/bin/env bash
# Regenerate examples/*.png from public-domain source photographs.
#
# Sources are downloaded into examples/source/ (git-ignored) rather than
# committed, so only the mosaics this tool produced live in the repository.
set -euo pipefail
cd "$(dirname "$0")"

mkdir -p examples/source

# Rear Admiral Grace Hopper, US Navy photograph, public domain. Mirrored here
# from matplotlib's sample data, which takes it from Wikimedia Commons:
# https://commons.wikimedia.org/wiki/File:Grace_Hopper.jpg
fetch() {
  local url="$1" out="$2"
  if [[ -f "$out" ]]; then
    return
  fi
  echo "fetching $out"
  curl -fsSL --retry 3 -o "$out" "$url"
}

fetch \
  "https://raw.githubusercontent.com/matplotlib/matplotlib/main/lib/matplotlib/mpl-data/sample_data/grace_hopper.jpg" \
  examples/source/grace_hopper.jpg

cargo build --release --quiet

run() {
  ./target/release/dice-dither "$@"
}

# The headline picture: black and white dice, Floyd-Steinberg.
run examples/source/grace_hopper.jpg \
  --cells 80 --cell-px 14 \
  -o examples/grace-hopper-dice.png \
  --sheet examples/grace-hopper-dice.txt \
  --inventory

# Big dice, so the faces themselves are readable.
run examples/source/grace_hopper.jpg \
  --cells 14 --cell-px 64 \
  -o examples/grace-hopper-detail.png

# One colour of die only: the pip count alone carries the picture, the way a
# newspaper halftone works. Bigger pips buy back some of the lost contrast.
run examples/source/grace_hopper.jpg \
  --cells 72 --cell-px 14 \
  --palette dark --pip-radius 0.12 --pip-spread 0.26 \
  -o examples/grace-hopper-halftone.png

echo "wrote examples/*.png"

#!/usr/bin/env bash
# Records the demo: builds liquid, drives it with scripted mouse and keyboard
# input while asciinema records, and converts the recording to a GIF with agg.
#
# Usage: demo/record.sh [OUTPUT_PREFIX]
#
# Writes OUTPUT_PREFIX.cast and OUTPUT_PREFIX.gif (default: demo.cast and
# demo.gif in the current directory). Needs Go, Python 3, asciinema 3, and agg.
# If gifsicle is installed, it also optimizes the GIF.
#
# GitHub serves images in pull requests and READMEs through a proxy that
# rejects files over 5 MiB, so the script warns when the GIF is bigger.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
out="${1:-demo}"
bin_dir="$(mktemp -d)"
trap 'rm -rf "${bin_dir}"' EXIT

(cd "${here}/.." && go build -o "${bin_dir}/liquid" .)
python3 "${here}/drive.py" "${bin_dir}/liquid" "${out}.cast"
agg --line-height 1.0 --font-size 14 --fps-cap 15 --idle-time-limit 2 \
  "${out}.cast" "${out}.gif"
if command -v gifsicle >/dev/null; then
  gifsicle --batch -O3 "${out}.gif"
fi

size=$(wc -c <"${out}.gif")
echo "wrote ${out}.cast and ${out}.gif (${size} bytes)"
if [ "${size}" -gt 5242880 ]; then
  echo "warning: ${out}.gif is over 5 MiB; GitHub won't display it" >&2
fi

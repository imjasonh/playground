#!/usr/bin/env bash
# Records the demo: builds liquid, drives it with scripted mouse and keyboard
# input while asciinema records, and converts the recording to a GIF with agg.
#
# Usage: demo/record.sh [OUTPUT_PREFIX]
#
# Writes OUTPUT_PREFIX.cast and OUTPUT_PREFIX.gif (default: demo.cast and
# demo.gif in the current directory). Needs Go, Python 3, asciinema 3, and agg.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
out="${1:-demo}"
bin_dir="$(mktemp -d)"
trap 'rm -rf "${bin_dir}"' EXIT

(cd "${here}/.." && go build -o "${bin_dir}/liquid" .)
python3 "${here}/drive.py" "${bin_dir}/liquid" "${out}.cast"
agg --line-height 1.0 --font-size 14 --fps-cap 20 --idle-time-limit 2 \
  "${out}.cast" "${out}.gif"
echo "wrote ${out}.cast and ${out}.gif"

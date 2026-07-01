#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
mkdir -p assets

ffmpeg -y -hide_banner -loglevel error \
  -f lavfi -i "testsrc2=size=480x270:rate=30" \
  -f lavfi -i "sine=frequency=523.25:sample_rate=44100" \
  -t 4 -shortest \
  -c:v mpeg1video -q:v 4 -bf 0 -g 15 \
  -c:a mp2 -b:a 128k -ar 44100 -ac 2 \
  -muxdelay 0.001 -f mpegts assets/demo.ts

echo "Generated assets/demo.ts"

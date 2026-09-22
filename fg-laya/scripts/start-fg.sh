#!/usr/bin/env bash
# Start FlightGear already airborne, with the Laya addon and property servers.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export DISPLAY="${DISPLAY:-:1}"
export LIBGL_ALWAYS_SOFTWARE="${LIBGL_ALWAYS_SOFTWARE:-1}"
export FG_HOME="${FG_HOME:-$ROOT/.fgfs-home}"
mkdir -p "$FG_HOME"

exec fgfs \
  --fg-home="$FG_HOME" \
  --aircraft=c172p \
  --disable-terrasync \
  --disable-ai-traffic \
  --disable-ai-models \
  --disable-sound \
  --disable-auto-coordination \
  --disable-random-objects \
  --disable-real-weather-fetch \
  --fog-disable \
  --timeofday=noon \
  --in-air \
  --altitude=3500 \
  --vc=100 \
  --heading=0 \
  --lat=37.55 \
  --lon=-122.65 \
  --geometry=1280x720 \
  --prop:/sim/rendering/shaders/quality-level=0 \
  --prop:/sim/rendering/multi-sample-buffers=0 \
  --prop:/sim/startup/save-on-exit=false \
  --ignore-autosave \
  --httpd=9146 \
  --telnet=socket,bi,60,127.0.0.1,5501,tcp \
  --addon="$ROOT/addon" \
  --prop:/sim/menubar/visibility=false \
  "$@"

#!/usr/bin/env bash
# Start FlightGear already airborne, with the property servers the Node loop uses.
# Ubuntu 2020.3 has no --addon or --fg-home; FG_HOME is the environment variable.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export PATH="/usr/games:$PATH"
export DISPLAY="${DISPLAY:-:1}"
export LIBGL_ALWAYS_SOFTWARE="${LIBGL_ALWAYS_SOFTWARE:-1}"
export XDG_RUNTIME_DIR="${XDG_RUNTIME_DIR:-/tmp/runtime-$USER}"
export FG_HOME="${FG_HOME:-$ROOT/.fgfs-home}"
mkdir -p "$FG_HOME" "$XDG_RUNTIME_DIR"

exec fgfs \
  --aircraft=c172p \
  --disable-terrasync \
  --disable-sound \
  --disable-auto-coordination \
  --disable-random-objects \
  --disable-real-weather-fetch \
  --disable-save-on-exit \
  --fog-disable \
  --timeofday=noon \
  --in-air \
  --altitude=3500 \
  --vc=105 \
  --heading=90 \
  --lat=37.576 \
  --lon=-122.65 \
  --geometry=1280x720 \
  --prop:/sim/rendering/shaders/quality-level=0 \
  --prop:/sim/rendering/multi-sample-buffers=0 \
  --prop:/sim/startup/save-on-exit=false \
  --prop:/sim/menubar/visibility=false \
  --prop:/controls/switches/magnetos=3 \
  --prop:/controls/engines/engine/mixture=1 \
  --prop:/fdm/jsbsim/propulsion/set-running=-1 \
  --prop:/sim/current-view/view-number=2 \
  --httpd=9146 \
  --telnet=5501 \
  "$@"

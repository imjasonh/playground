#!/usr/bin/env bash
# Build all three cards, then compose the still triptych and the animated one.
#
# Usage: ./triptych.sh
#
# Writes triptych.png (frame 0 of each card, side by side), triptych.gif (the
# idle loop at a third of the size) and triptych.mp4 (the loop at half size).
# The frames it renders on the way stay in frames/.
#
# Needs the klad binary (see build.sh for how to get it): set KLAD=/path/to/klad
# or put `klad` on your PATH, and KLAD_FONTS if the binary can't find its fonts.
# Needs ffmpeg to put the panels side by side and to encode the loop. STILL=1
# stops after triptych.png.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
python="${PYTHON:-python3}"

klad="${KLAD:-$(command -v klad || true)}"
if [ -z "$klad" ]; then
  echo "klad not found: build it from https://github.com/klad-app/klad and set KLAD=/path/to/klad, or put klad on your PATH" >&2
  exit 1
fi
if ! command -v ffmpeg >/dev/null; then
  echo "ffmpeg not found: it puts the panels side by side and encodes the loop" >&2
  exit 1
fi

# One panel per archetype, left to right, in story order. The cards don't
# depend on each other, so they build at the same time.
cards=(robot astronaut alien)
pids=()
for name in "${cards[@]}"; do
  FORCE=1 "$here/build.sh" "$name" >/dev/null &
  pids+=("$!")
done
for pid in "${pids[@]}"; do
  wait "$pid"
done

# Three panels in a row on a dark mat. At full size a panel is 1024x1280, the
# gutter is 40px, and the margin is 48px at the sides and 64px above and
# below, which makes 3248x1408. $1 scales all of that.
row() {
  "$python" - "$1" <<'EOF'
import sys

k = float(sys.argv[1])
w, h, gutter, side, top = (round(v * k) for v in (1024, 1280, 40, 48, 64))
mat = "color=0x0b0920"
print(f"[0:v]pad={side + w}:{h + 2 * top}:{side}:{top}:{mat}[a];"
      f"[1:v]pad={gutter + w}:{h + 2 * top}:{gutter}:{top}:{mat}[b];"
      f"[2:v]pad={gutter + w + side}:{h + 2 * top}:{gutter}:{top}:{mat}[c];"
      "[a][b][c]hstack=inputs=3")
EOF
}

ffmpeg -loglevel error -y \
  -i "$here/robot.png" -i "$here/astronaut.png" -i "$here/alien.png" \
  -filter_complex "$(row 1)" "$here/triptych.png"
echo "built $here/triptych.png"

if [ "${STILL:-0}" = 1 ]; then
  exit 0
fi

# Every frame of the loop, at half size. A frame only moves layers that are
# already painted, so klad draws each from its cache.
read -r frames fps < <(cd "$here" && "$python" -c 'import kit; print(kit.FRAMES, kit.FPS)')
for name in "${cards[@]}"; do
  mkdir -p "$here/frames/$name"
  seq 0 $((frames - 1)) | xargs -P 4 -I{} sh -c \
    '"$0" render "$1" --frame "$3" --scale 0.5 -o "$2/$(printf %03d "$3").png" >/dev/null' \
    "$klad" "$here/$name.klad" "$here/frames/$name" {}
done

inputs=()
for name in "${cards[@]}"; do
  inputs+=(-framerate "$fps" -i "$here/frames/$name/%03d.png")
done

ffmpeg -loglevel error -y "${inputs[@]}" \
  -filter_complex "$(row 0.5),format=yuv420p" \
  -c:v libx264 -crf 20 -movflags +faststart "$here/triptych.mp4"

# A GIF holds 256 colours. An ordered dither keeps still areas the same from
# frame to frame, so the encoder stores only what moved.
ffmpeg -loglevel error -y "${inputs[@]}" \
  -filter_complex "$(row 0.5),scale=iw*2/3:-1:flags=lanczos,split[x][y];[x]palettegen=stats_mode=diff[p];[y][p]paletteuse=dither=bayer:bayer_scale=4:diff_mode=rectangle" \
  "$here/triptych.gif"
echo "built $here/triptych.mp4 and $here/triptych.gif"

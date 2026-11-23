#!/usr/bin/env bash
# Export One Tap Quest for Web (build/web/) and iOS PCK (../ios/Sources/Experiments/OneTapQuest/Resources/).
# Usage:
#   GODOT=/path/to/godot bash one-tap-quest/build.sh [web|pck|all]
set -euo pipefail

mode="${1:-all}"
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/.." && pwd)
godot="${GODOT:-godot}"

if ! command -v "$godot" >/dev/null 2>&1 && [ ! -x "$godot" ]; then
  echo "error: godot binary not found (set GODOT=/path/to/godot)" >&2
  exit 1
fi

"$godot" --headless --editor --path "$script_dir" --import --quit >/dev/null 2>&1 || true

if [ "$mode" = "pck" ] || [ "$mode" = "all" ]; then
  out_ios="$repo_root/ios/Sources/Experiments/OneTapQuest/Resources"
  mkdir -p "$out_ios"
  "$godot" --headless --path "$script_dir" --export-pack "Web" "$out_ios/one-tap-quest.pck"
  echo "Exported iOS PCK to $out_ios/one-tap-quest.pck"
fi

if [ "$mode" = "web" ] || [ "$mode" = "all" ]; then
  out_web="$script_dir/build/web"
  rm -rf "$out_web"
  mkdir -p "$out_web"
  touch "$script_dir/build/.gdignore"
  "$godot" --headless --path "$script_dir" --export-release "Web" "$out_web/index.html"
  cp -L "$script_dir/whbiab.js" "$out_web/whbiab.js"
  echo "Exported Web build to $out_web"
fi

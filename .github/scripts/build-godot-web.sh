#!/usr/bin/env bash
# Export a Godot project's Web preset into a destination directory for Pages.
#
# Usage:
#   build-godot-web.sh <app_dir> <dest_dir>
set -euo pipefail

app_dir="${1:?usage: build-godot-web.sh <app_dir> <dest_dir>}"
dest_dir="${2:?usage: build-godot-web.sh <app_dir> <dest_dir>}"

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
godot="${GODOT:-}"
if [ -z "$godot" ]; then
  godot=$(bash "$script_dir/setup-godot.sh")
fi

abs_app=$(cd "$app_dir" && pwd)
mkdir -p "$dest_dir"
abs_dest=$(cd "$dest_dir" && pwd)

# Clear any raw source files that cp -rL placed in dest_dir before exporting.
rm -rf "${abs_dest:?}"/*

"$godot" --headless --editor --path "$abs_app" --import --quit >/dev/null 2>&1 || true
"$godot" --headless --path "$abs_app" --export-release "Web" "$abs_dest/index.html"

if [ -e "$abs_app/whbiab.js" ]; then
  cp -L "$abs_app/whbiab.js" "$abs_dest/whbiab.js"
fi

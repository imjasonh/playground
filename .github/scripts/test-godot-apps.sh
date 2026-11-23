#!/usr/bin/env bash
# Run headless GDScript tests and verify Web + PCK exports for Godot apps listed
# in GODOT_APPS (JSON array).
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
cd "$repo_root"

apps=()
while IFS= read -r app; do
  [ -n "$app" ] && apps+=("$app")
done < <(printf '%s' "${GODOT_APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No Godot apps changed. Nothing to do."
  exit 0
fi

godot="${GODOT:-}"
if [ -z "$godot" ]; then
  godot=$(bash "$script_dir/setup-godot.sh")
fi

for app in "${apps[@]}"; do
  echo "::group::Godot test & export: ${app}"
  "$godot" --headless --editor --path "$app" --import --quit >/dev/null 2>&1 || true

  if [ -d "$app/tests" ]; then
    for test_file in "$app"/tests/test_*.gd; do
      [ -f "$test_file" ] || continue
      rel="${test_file#"$app/"}"
      echo "Running res://${rel}..."
      "$godot" --headless --path "$app" --script "res://${rel}"
    done
  fi

  if [ -f "$app/export_presets.cfg" ]; then
    tmp_out="$(mktemp -d)"
    trap 'rm -rf "$tmp_out"' EXIT
    GODOT="$godot" bash "$script_dir/build-godot-web.sh" "$app" "$tmp_out/web"
    for f in index.html index.js index.wasm index.pck; do
      if [ ! -s "$tmp_out/web/$f" ]; then
        echo "FAIL: missing or empty Web export file: $f" >&2
        exit 1
      fi
    done
    "$godot" --headless --path "$app" --export-pack "Web" "$tmp_out/game.pck"
    if [ ! -s "$tmp_out/game.pck" ]; then
      echo "FAIL: missing or empty PCK export" >&2
      exit 1
    fi
    rm -rf "$tmp_out"
    trap - EXIT
  fi
  echo "::endgroup::"
done

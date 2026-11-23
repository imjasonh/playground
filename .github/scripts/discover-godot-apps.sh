#!/usr/bin/env bash
# Discover top-level Godot game directories (those with a root project.godot).
#
# Usage:
#   discover-godot-apps.sh --all
#   git diff --name-only ... | discover-godot-apps.sh --from-changes
set -euo pipefail

mode="${1:-}"
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

is_godot_app() {
  local dir="$1"
  [[ -n "$dir" && "$dir" != .* && -f "$dir/project.godot" ]]
}

apps=()
case "$mode" in
  --all)
    for d in */; do
      app="${d%/}"
      if is_godot_app "$app"; then
        apps+=("$app")
      fi
    done
    ;;
  --from-changes)
    declare -A seen=()
    while IFS= read -r path; do
      [ -z "$path" ] && continue
      top="${path%%/*}"
      if [ -z "${seen[$top]:-}" ] && is_godot_app "$top"; then
        seen[$top]=1
        apps+=("$top")
      fi
    done
    ;;
  *)
    echo "usage: discover-godot-apps.sh --all|--from-changes" >&2
    exit 2
    ;;
esac

if [ "${#apps[@]}" -eq 0 ]; then
  echo "[]"
else
  printf '%s\n' "${apps[@]}" | sort -u | jq -R . | jq -cs .
fi

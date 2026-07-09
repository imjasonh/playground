#!/usr/bin/env bash
# Discover top-level browser app directories and emit a JSON array.
#
# A browser app is a non-hidden top-level directory containing index.html —
# the same definition the deploy and preview workflows use to decide what to
# publish. (This is broader than discover-testable-apps.sh, which also requires
# package.json with a "test" script.)
#
# Usage:
#   discover-browser-apps.sh --all
#     List every browser app in the repo.
#
#   discover-browser-apps.sh --from-changes [path...]
#     List browser apps touched by the given paths (or stdin when no args).
#     Only top-level directories are considered; e.g. kanoodle/src/app.js → kanoodle.
set -euo pipefail

is_browser_app() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  [[ -f "$name/index.html" ]]
}

emit_json() {
  local -n list=$1
  if ((${#list[@]} == 0)); then
    echo '[]'
  else
    printf '%s\n' "${list[@]}" | sort -u | jq -R . | jq -cs .
  fi
}

collect_all_browser_apps() {
  local apps=()
  for dir in */; do
    local name="${dir%/}"
    if is_browser_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

collect_browser_apps_from_changes() {
  local paths=()
  if (("$#" > 0)); then
    paths=("$@")
  else
    while IFS= read -r path; do
      paths+=("$path")
    done
  fi

  local apps=()
  local path name
  declare -A seen=()
  for path in "${paths[@]}"; do
    [[ -z "$path" ]] && continue
    [[ "$path" != */* ]] && continue
    name="${path%%/*}"
    if [[ -n "${seen[$name]+x}" ]]; then
      continue
    fi
    seen["$name"]=1
    if is_browser_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    collect_all_browser_apps
    ;;
  --from-changes)
    shift
    collect_browser_apps_from_changes "$@"
    ;;
  *)
    echo "Usage: $0 --all | --from-changes [path...]" >&2
    exit 1
    ;;
esac

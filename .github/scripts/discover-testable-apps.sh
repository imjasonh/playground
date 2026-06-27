#!/usr/bin/env bash
# Discover testable app directories and emit a JSON array.
#
# An app is testable when it has index.html, package.json, and a "test" script
# (same app definition as deploy/preview workflows).
#
# Usage:
#   discover-testable-apps.sh --all
#     List every testable app in the repo.
#
#   discover-testable-apps.sh --from-changes [path...]
#     List testable apps touched by the given paths (or stdin when no args).
#     Only top-level directories are considered; e.g. kanoodle/src/app.js → kanoodle.
set -euo pipefail

is_testable_app() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  if [[ ! -f "$name/index.html" || ! -f "$name/package.json" ]]; then
    return 1
  fi

  node -e "
    const pkg = require('./${name}/package.json');
    process.exit(pkg.scripts && pkg.scripts.test ? 0 : 1);
  " 2>/dev/null
}

emit_json() {
  local -n list=$1
  if ((${#list[@]} == 0)); then
    echo '[]'
  else
    printf '%s\n' "${list[@]}" | sort -u | jq -R . | jq -cs .
  fi
}

collect_all_testable_apps() {
  local apps=()
  for dir in */; do
    local name="${dir%/}"
    if is_testable_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

collect_testable_from_changes() {
  local paths=()
  if (("$#" > 0)); then
    paths=("$@")
  else
    while IFS= read -r path; do
      paths+=("$path")
    done
  fi

  local apps=()
  local seen=$'\n'
  local path name
  for path in "${paths[@]}"; do
    [[ -z "$path" ]] && continue
    [[ "$path" != */* ]] && continue
    name="${path%%/*}"
    if [[ "$seen" == *$'\n'"$name"$'\n'* ]]; then
      continue
    fi
    seen+="$name"$'\n'
    if is_testable_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    collect_all_testable_apps
    ;;
  --from-changes)
    shift
    collect_testable_from_changes "$@"
    ;;
  *)
    echo "Usage: $0 --all | --from-changes [path...]" >&2
    exit 1
    ;;
esac

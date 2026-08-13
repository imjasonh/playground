#!/usr/bin/env bash
# Discover top-level JavaScript/TypeScript Cloudflare Worker app directories
# and emit a JSON array.
#
# A JS Worker is a non-hidden top-level directory containing wrangler.toml and
# a package.json with a "test" script, but no Cargo.toml (Rust Workers are
# tested by the rust leg instead).
#
# Usage:
#   discover-js-workers.sh --all
#     List every JS Worker app in the repo.
#
#   discover-js-workers.sh --from-changes [path...]
#     List JS Worker apps touched by the given paths (or stdin when no args).
set -euo pipefail

is_js_worker() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  [[ -f "$name/wrangler.toml" ]] || return 1
  [[ -f "$name/Cargo.toml" ]] && return 1
  [[ -f "$name/package.json" ]] || return 1

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

collect_all_js_workers() {
  local apps=()
  for dir in */; do
    local name="${dir%/}"
    if is_js_worker "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

collect_js_workers_from_changes() {
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
    if is_js_worker "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    collect_all_js_workers
    ;;
  --from-changes)
    shift
    collect_js_workers_from_changes "$@"
    ;;
  *)
    echo "Usage: $0 --all | --from-changes [path...]" >&2
    exit 1
    ;;
esac

#!/usr/bin/env bash
# Discover top-level Rust app directories and emit a JSON array.
#
# A Rust app is a non-hidden top-level directory containing Cargo.toml.
#
# Usage:
#   discover-rust-apps.sh --all
#     List every Rust app in the repo.
#
#   discover-rust-apps.sh --from-changes [path...]
#     List Rust apps touched by the given paths (or stdin when no args).
set -euo pipefail

is_rust_app() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  [[ -f "$name/Cargo.toml" ]]
}

emit_json() {
  local -n list=$1
  if ((${#list[@]} == 0)); then
    echo '[]'
  else
    printf '%s\n' "${list[@]}" | sort -u | jq -R . | jq -cs .
  fi
}

collect_all_rust_apps() {
  local apps=()
  for dir in */; do
    local name="${dir%/}"
    if is_rust_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

collect_rust_apps_from_changes() {
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
    if is_rust_app "$name"; then
      apps+=("$name")
    fi
  done
  emit_json apps
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    collect_all_rust_apps
    ;;
  --from-changes)
    shift
    collect_rust_apps_from_changes "$@"
    ;;
  *)
    echo "Usage: $0 --all | --from-changes [path...]" >&2
    exit 1
    ;;
esac

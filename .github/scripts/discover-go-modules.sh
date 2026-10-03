#!/usr/bin/env bash
# Discover top-level Go module directories and emit a JSON array.
#
# A Go app is a non-hidden top-level directory containing go.mod.
#
# Usage:
#   discover-go-modules.sh --all
#     List every Go app module in the repo.
#
#   discover-go-modules.sh --from-changes [path...]
#     List Go app modules touched by the given paths (or stdin when no args),
#     and the modules whose go.mod replaces a touched directory's module with
#     a relative path (git-k8s builds against ../kube), so a change to a
#     library also tests the apps that use it at head.
set -euo pipefail

is_go_module() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  [[ -f "$name/go.mod" ]]
}

emit_json() {
  local -n list=$1
  if ((${#list[@]} == 0)); then
    echo '[]'
  else
    printf '%s\n' "${list[@]}" | sort -u | jq -R . | jq -cs .
  fi
}

collect_all_go_modules() {
  local modules=()
  for dir in */; do
    local name="${dir%/}"
    if is_go_module "$name"; then
      modules+=("$name")
    fi
  done
  emit_json modules
}

# dependents prints the Go modules whose go.mod has a replace directive that
# points at the top-level directory $1.
dependents() {
  local lib="$1" dir
  for dir in */; do
    dir="${dir%/}"
    if [[ "$dir" != "$lib" ]] && is_go_module "$dir" &&
      grep -Eq "=>[[:space:]]*\.\./${lib}/?([[:space:]]|$)" "$dir/go.mod"; then
      echo "$dir"
    fi
  done
}

collect_go_modules_from_changes() {
  local paths=()
  if (("$#" > 0)); then
    paths=("$@")
  else
    while IFS= read -r path; do
      paths+=("$path")
    done
  fi

  local modules=()
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
    if is_go_module "$name"; then
      modules+=("$name")
    fi
    while IFS= read -r dependent; do
      modules+=("$dependent")
    done < <(dependents "$name")
  done
  emit_json modules
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    collect_all_go_modules
    ;;
  --from-changes)
    shift
    collect_go_modules_from_changes "$@"
    ;;
  *)
    echo "Usage: $0 --all | --from-changes [path...]" >&2
    exit 1
    ;;
esac

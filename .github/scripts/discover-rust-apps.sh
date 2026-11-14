#!/usr/bin/env bash
# Discover top-level Rust app directories and emit a JSON array.
#
# A Rust app is a non-hidden top-level directory containing Cargo.toml. A
# top-level directory that is another kind of app can also hold a Rust library
# crate in its rust/ subdirectory (wehadababyitsaboy/rust). That crate is
# listed by its path, such as wehadababyitsaboy/rust, a change under the rust/
# directory selects it, and so does a change to any app that depends on it with
# a path dependency.
#
# Usage:
#   discover-rust-apps.sh --all
#     List every Rust app in the repo.
#
#   discover-rust-apps.sh --from-changes [path...]
#     List Rust apps touched by the given paths (or stdin when no args). A
#     change under .github/wrangler/ (the pinned Wrangler version) selects
#     every Cloudflare Worker app, since all of them build and deploy with it.
#     A change to the scripts that test Rust apps selects every Rust app.
set -euo pipefail

is_rust_app() {
  local name="$1"

  if [[ "$name" == .* ]]; then
    return 1
  fi

  # ESP32 firmware uses the espup Xtensa toolchain and ESP-IDF, so it cannot
  # run through the generic stable-Rust job. inkbot-esp32.yml / esp32-ble.yml
  # own those host lib tests and Xtensa cross-builds instead.
  if [[ "$name" == "inkbot-esp32" || "$name" == "esp32-ble" ]]; then
    return 1
  fi

  [[ -f "$name/Cargo.toml" ]]
}

# crate_for_path prints the crate a changed path belongs to: the top-level
# directory, or its rust/ subdirectory when that holds a crate and the path is
# inside it.
crate_for_path() {
  local path="$1" name
  name="${path%%/*}"
  if [[ "$path" == "$name/rust/"* ]] && is_rust_app "$name/rust"; then
    echo "$name/rust"
  else
    echo "$name"
  fi
}

# every_rust_app prints each Rust app, nested library crates included.
every_rust_app() {
  local dir name
  for dir in */; do
    name="${dir%/}"
    if is_rust_app "$name"; then
      echo "$name"
    fi
    if is_rust_app "$name/rust"; then
      echo "$name/rust"
    fi
  done
}

# dependents prints the Rust apps whose Cargo.toml has a path dependency on the
# crate directory $1.
dependents() {
  local lib="$1" dir
  for dir in */; do
    dir="${dir%/}"
    if [[ "$dir" != "$lib" ]] && is_rust_app "$dir" &&
      grep -Eq "path[[:space:]]*=[[:space:]]*\"\.\./${lib}/?\"" "$dir/Cargo.toml"; then
      echo "$dir"
    fi
  done
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
  mapfile -t apps < <(every_rust_app)
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
    if [[ "$path" == .github/wrangler/* ]]; then
      while IFS= read -r name; do
        if [[ -f "$name/wrangler.toml" ]]; then
          apps+=("$name")
        fi
      done < <(every_rust_app)
      continue
    fi
    if [[ "$path" == .github/scripts/test-rust-apps.sh || "$path" == .github/scripts/check-worker-deploy-build.sh ]]; then
      mapfile -t apps < <(every_rust_app)
      continue
    fi
    [[ "$path" != */* ]] && continue
    name=$(crate_for_path "$path")
    if [[ -n "${seen[$name]+x}" ]]; then
      continue
    fi
    seen["$name"]=1
    if is_rust_app "$name"; then
      apps+=("$name")
    fi
    while IFS= read -r dependent; do
      apps+=("$dependent")
    done < <(dependents "$name")
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

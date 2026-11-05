#!/usr/bin/env bash
# Drop Cargo build outputs that the current lockfiles do not need.
#
# test.yml builds every Rust app into one target directory and restores it
# on the next run. Cargo never trims target/, so that directory would keep
# every app crate ever compiled (they change every commit) and every old
# dependency version. This leaves the dependency artifacts and the registry
# sources the current Cargo.lock files name.
#
# Cargo fingerprints name a dependency by its package name plus a hash, with
# hyphens in fingerprint and build directories and underscores in deps/.
# The app crates themselves are removed, so the next run recompiles those
# and reuses the dependencies.
#
# Usage:
#   prune-cargo-cache.sh TARGET_DIR [REGISTRY_DIR]
#
# CARGO_LOCK_ROOT overrides the repository root the lockfiles are read from,
# which lets tests point the script at a fixture.
set -euo pipefail

if (($# < 1 || $# > 2)); then
  echo "Usage: $0 TARGET_DIR [REGISTRY_DIR]" >&2
  exit 2
fi

target=$1
registry=${2:-}

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
lock_root=${CARGO_LOCK_ROOT:-$repo_root}

bytes() {
  if [[ -e "$1" ]]; then
    du -sb "$1" | cut -f1
  else
    echo 0
  fi
}

# Package names and name-versions from every Cargo.lock, minus each app's own
# package. inkbot-esp32 and esp32-ble are built by their own workflows.
declare -A workspace=()
declare -A keep_pkg=()
declare -A keep_dep=()
declare -A keep_crate=()

shopt -s nullglob
for lock in "$lock_root"/*/Cargo.lock; do
  app=$(basename "$(dirname "$lock")")
  case "$app" in
    .* | inkbot-esp32 | esp32-ble) continue ;;
  esac
  manifest="$(dirname "$lock")/Cargo.toml"
  if [[ -f "$manifest" ]]; then
    name=$(awk '
      /^\[/ { section = $0 }
      section == "[package]" && $1 == "name" {
        gsub(/"/, "", $3)
        print $3
        exit
      }
    ' "$manifest")
    [[ -n "$name" ]] && workspace["$name"]=1
  fi
done

for lock in "$lock_root"/*/Cargo.lock; do
  app=$(basename "$(dirname "$lock")")
  case "$app" in
    .* | inkbot-esp32 | esp32-ble) continue ;;
  esac
  while IFS=$'\t' read -r name version; do
    [[ -z "$name" || -n "${workspace[$name]+x}" ]] && continue
    keep_pkg["$name"]=1
    underscored=${name//-/_}
    keep_dep["$underscored"]=1
    keep_dep["lib${underscored}"]=1
    keep_crate["${name}-${version}"]=1
  done < <(awk '
    /^\[\[package\]\]/ { name = ""; version = "" }
    /^name = / {
      name = $3
      gsub(/"/, "", name)
    }
    /^version = / {
      version = $3
      gsub(/"/, "", version)
      if (name != "") print name "\t" version
    }
  ' "$lock")
done

# unit_key strips Cargo's trailing hash. aes-gcm-0123abcd becomes aes-gcm,
# and libserde-0123abcd.rlib becomes libserde.
unit_key() {
  local base=$1
  printf '%s\n' "${base%-*}"
}

prune_units() {
  local dir=$1 kind=$2 entry base key
  [[ -d "$dir" ]] || return 0
  shopt -s dotglob
  for entry in "$dir"/*; do
    [[ -e "$entry" ]] || continue
    base=$(basename "$entry")
    [[ "$base" == . || "$base" == .. ]] && continue
    key=$(unit_key "$base")
    case "$kind" in
      deps)
        [[ -n "${keep_dep[$key]+x}" ]] && continue
        ;;
      pkg)
        [[ -n "${keep_pkg[$key]+x}" ]] && continue
        ;;
    esac
    rm -rf "$entry"
  done
  shopt -u dotglob
}

if [[ -d "$target" ]]; then
  echo "cargo target before: $(bytes "$target") bytes"
  find "$target" -type d \( -name incremental -o -name examples -o -name tmp \) -prune -exec rm -rf {} +
  find "$target" -type f \
    ! -path '*/deps/*' ! -path '*/build/*' ! -path '*/.fingerprint/*' \
    ! -name '.rustc_info.json' ! -name 'CACHEDIR.TAG' \
    -delete
  while IFS= read -r dir; do
    case "$dir" in
      */deps/* | */build/* | */.fingerprint/*) continue ;;
    esac
    case "$(basename "$dir")" in
      deps) prune_units "$dir" deps ;;
      build | .fingerprint) prune_units "$dir" pkg ;;
    esac
  done < <(find "$target" -type d \( -name deps -o -name build -o -name .fingerprint \))
  echo "cargo target after: $(bytes "$target") bytes"
fi

if [[ -n "$registry" && -d "$registry" ]]; then
  echo "cargo registry before: $(bytes "$registry") bytes"
  # .crate files and extracted sources. The index stays; Cargo rebuilds it
  # cheaply, and pruning it file by file mis-handles the sparse index.
  while IFS= read -r entry; do
    base=$(basename "$entry")
    case "$entry" in
      */cache/*)
        [[ -n "${keep_crate[${base%.crate}]+x}" ]] && continue
        ;;
      */src/*)
        [[ -n "${keep_crate[$base]+x}" ]] && continue
        ;;
      *) continue ;;
    esac
    rm -rf "$entry"
  done < <(find "$registry/cache" "$registry/src" -mindepth 2 -maxdepth 2 2>/dev/null)
  echo "cargo registry after: $(bytes "$registry") bytes"
fi

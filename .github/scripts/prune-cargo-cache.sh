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
#   prune-cargo-cache.sh [-l LOCKFILE]... TARGET_DIR [REGISTRY_DIR]
#
# By default the script keeps what the Rust apps' Cargo.lock files name: one
# in each top-level directory and in each one's rust/ subdirectory, except the
# ESP32 firmware crates, whose test.yml jobs keep their own caches. Each -l
# names a lockfile to read instead. Those jobs pass their crate's lockfiles
# and, for a firmware build, the Rust standard library's, because
# `-Z build-std` compiles std and its dependencies into the target directory.
#
# CARGO_LOCK_ROOT overrides the repository root the default lockfiles are
# read from, which lets tests point the script at a fixture.
set -euo pipefail

usage() {
  echo "Usage: $0 [-l LOCKFILE]... TARGET_DIR [REGISTRY_DIR]" >&2
  exit 2
}

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
lock_root=${CARGO_LOCK_ROOT:-$(cd "$script_dir/../.." && pwd)}

locks=()
while getopts "l:" opt; do
  case "$opt" in
    l) locks+=("$OPTARG") ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))

if (($# < 1 || $# > 2)); then
  usage
fi

target=$1
registry=${2:-}

if ((${#locks[@]} == 0)); then
  declare -A esp32=()
  while IFS= read -r name; do
    esp32["$name"]=1
  done < <(cd "$lock_root" && bash "$script_dir/discover-esp32-apps.sh" --all | jq -r '.[]')
  shopt -s nullglob
  for lock in "$lock_root"/*/Cargo.lock "$lock_root"/*/rust/Cargo.lock; do
    rel=${lock#"$lock_root"/}
    app=${rel%%/*}
    [[ "$app" == .* || -n "${esp32[$app]+x}" ]] && continue
    locks+=("$lock")
  done
  shopt -u nullglob
fi

for lock in "${locks[@]}"; do
  if [[ ! -f "$lock" ]]; then
    echo "prune-cargo-cache.sh: no lockfile at $lock" >&2
    exit 1
  fi
done

bytes() {
  if [[ -e "$1" ]]; then
    du -sb "$1" | cut -f1
  else
    echo 0
  fi
}

# Package names and name-versions from every lockfile, minus each crate's own
# package.
declare -A workspace=()
declare -A keep_pkg=()
declare -A keep_dep=()
declare -A keep_crate=()

for lock in "${locks[@]}"; do
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

for lock in "${locks[@]}"; do
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

# unit_key strips Cargo's trailing hash. aes-gcm-0123456789abcdef becomes
# aes-gcm, and libserde-0123456789abcdef.rlib becomes libserde. Cargo 1.100
# and later lay out build/ as build/PACKAGE/HASH/, so a name without a hash
# is already the package name.
unit_key() {
  local base=$1
  if [[ "$base" =~ ^(.+)-[0-9a-f]{16}(\..*)?$ ]]; then
    printf '%s\n' "${BASH_REMATCH[1]}"
  else
    printf '%s\n' "$base"
  fi
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
  # Build script output keeps its own tmp and examples directories, such as
  # the CMake tree that esp-idf-sys builds ESP-IDF in, so leave build/ (and
  # deps/ and .fingerprint/) alone here.
  find "$target" \( -path "$target/*/build/*" -o -path "$target/*/deps/*" -o -path "$target/*/.fingerprint/*" \) -prune -o \
    -type d \( -name incremental -o -name examples -o -name tmp \) -prune -exec rm -rf {} +
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

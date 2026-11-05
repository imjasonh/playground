#!/usr/bin/env bash
# Bound the Go caches before test.yml saves them.
#
# The Test job restores the newest saved archive by key prefix, so without
# pruning each save holds everything earlier jobs downloaded and compiled.
# Go trims its build cache by age only (entries unused for five days) and
# never trims the module cache, so that archive grew by hundreds of MB a day
# until restoring it filled a runner's disk.
#
# After this script, the saved archive is a function of the current commit
# and a size budget:
#   - The module cache is emptied and refilled with `go mod download` in
#     every Go module, so it holds the versions the current go.sum files
#     name and nothing older.
#   - The build cache is trimmed to GO_BUILD_CACHE_BUDGET bytes (default
#     2 GiB), least recently used entries first. The go command sets an
#     entry's mtime when it uses it, and tar keeps mtimes, so mtime order is
#     use order across jobs.
#
# Usage:
#   prune-go-caches.sh           # module cache, then build cache
#   prune-go-caches.sh --build   # build cache only
#
# GOCACHE and GOMODCACHE override `go env`, which lets tests point the
# script at temporary directories.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)

build_budget="${GO_BUILD_CACHE_BUDGET:-$((2 * 1024 * 1024 * 1024))}"

bytes() {
  if [[ -e "$1" ]]; then
    du -sb "$1" | cut -f1
  else
    echo 0
  fi
}

# refill_module_cache replaces the module cache with the modules that the
# repository's go.sum files name.
refill_module_cache() {
  local modcache="${GOMODCACHE:-$(go env GOMODCACHE)}"
  echo "module cache before: $(bytes "$modcache") bytes"
  go clean -modcache
  local module
  while IFS= read -r module; do
    echo "go mod download in ${module}"
    (cd "${repo_root}/${module}" && go mod download)
  done < <(bash "${repo_root}/.github/scripts/discover-go-modules.sh" --all | jq -r '.[]')
  echo "module cache after: $(bytes "$modcache") bytes"
}

# trim_build_cache deletes the least recently used build cache entries until
# the entries fit in the budget. Only the entry files under the 256 two-digit
# subdirectories are candidates; trim.txt, README, and fuzz/ are left alone,
# as in the go command's own trim.
trim_build_cache() {
  local cache="${GOCACHE:-$(go env GOCACHE)}"
  echo "build cache before: $(bytes "$cache") bytes (budget ${build_budget})"
  if [[ ! -d "$cache" ]]; then
    return
  fi
  find "$cache" -mindepth 2 -maxdepth 2 -type f \
    -regex '.*/[0-9a-f][0-9a-f]/[^/]*' -printf '%T@\t%s\t%p\n' |
    sort -n |
    awk -F'\t' -v budget="$build_budget" '
      { size[NR] = $2; path[NR] = $3; total += $2 }
      END {
        for (i = 1; i <= NR && total > budget; i++) {
          print path[i]
          total -= size[i]
        }
      }' |
    tr '\n' '\0' | xargs -0 -r rm -f
  echo "build cache after: $(bytes "$cache") bytes"
}

case "${1:-}" in
  "")
    refill_module_cache
    trim_build_cache
    ;;
  --build)
    trim_build_cache
    ;;
  *)
    echo "Usage: $0 [--build]" >&2
    exit 2
    ;;
esac

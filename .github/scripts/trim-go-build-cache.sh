#!/usr/bin/env bash
# Trim the Go build cache to a byte budget before test.yml saves it.
#
# The Test job restores the newest saved archive by key prefix, so without a
# bound each save holds everything earlier jobs compiled. Go trims its build
# cache by age only (entries unused for five days), which doesn't bound the
# size of one archive.
#
# This script deletes the least recently used entries until the rest fit in
# GO_BUILD_CACHE_BUDGET bytes (default 3 GiB). The go command sets an entry's
# mtime when it uses it, and tar keeps mtimes, so mtime order is use order
# across jobs. Only the entry files under the 256 two-digit subdirectories
# are candidates; trim.txt, README, and fuzz/ are left alone, as in the go
# command's own trim.
#
# GOCACHE overrides `go env GOCACHE`, which lets tests point the script at a
# temporary directory.
set -euo pipefail

budget="${GO_BUILD_CACHE_BUDGET:-$((3 * 1024 * 1024 * 1024))}"
cache="${GOCACHE:-$(go env GOCACHE)}"

bytes() {
  if [[ -e "$1" ]]; then
    du -sb "$1" | cut -f1
  else
    echo 0
  fi
}

echo "build cache before: $(bytes "$cache") bytes (budget ${budget})"
if [[ ! -d "$cache" ]]; then
  exit 0
fi
find "$cache" -mindepth 2 -maxdepth 2 -type f \
  -regex '.*/[0-9a-f][0-9a-f]/[^/]*' -printf '%T@\t%s\t%p\n' |
  sort -n |
  awk -F'\t' -v budget="$budget" '
    { size[NR] = $2; path[NR] = $3; total += $2 }
    END {
      for (i = 1; i <= NR && total > budget; i++) {
        print path[i]
        total -= size[i]
      }
    }' |
  tr '\n' '\0' | xargs -0 -r rm -f
echo "build cache after: $(bytes "$cache") bytes"

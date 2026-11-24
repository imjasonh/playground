#!/usr/bin/env bash
# Trim pasta's cache to what one run used before test.yml saves it.
#
# Usage: trim-pasta-cache.sh MARKER
#
# pasta stores per-file results and parse trees under <cache>/v<N>/ and
# prunes them only past 1 GiB, so a cache restored by key prefix and saved
# again would keep the results of every older version of every file. pasta
# sets an entry's mtime when it reads or writes it, and tar keeps mtimes, so
# an entry no newer than MARKER, a file touched before the run, went unused.
# This script deletes those entries and the directories they leave empty.
# wazero/ (compiled grammars) and modules/ (fetched rule modules) are left
# alone.
#
# PASTA_CACHE overrides the cache directory, which defaults to
# ${XDG_CACHE_HOME:-$HOME/.cache}/pasta, so tests can point the script at a
# temporary directory.
set -euo pipefail

marker="$1"
cache="${PASTA_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/pasta}"

bytes() {
  if [[ -e "$1" ]]; then
    du -sb "$1" | cut -f1
  else
    echo 0
  fi
}

echo "pasta cache before: $(bytes "$cache") bytes"
if [[ ! -d "$cache" ]]; then
  exit 0
fi
find "$cache" -mindepth 1 -maxdepth 1 -type d -name 'v[0-9]*' -print0 |
  while IFS= read -r -d '' dir; do
    find "$dir" -type f ! -newer "$marker" -delete
    find "$dir" -type d -empty -delete
  done
echo "pasta cache after: $(bytes "$cache") bytes"

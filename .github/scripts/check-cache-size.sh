#!/usr/bin/env bash
# Refuse to save an Actions cache that is larger than its budget.
#
# A GitHub-hosted runner guarantees about 14 GB of free disk, and
# actions/cache keeps the compressed archive on disk while it extracts, so
# a large archive fails the job that restores it before any step runs.
# Gate every cache save on this script, so an archive over budget is never
# written. Run it after the step that trims the cache, and before
# actions/cache/save.
#
# Usage:
#   check-cache-size.sh MAX_BYTES PATH...
#
# Prints the size of each path. Exits 1 when the total exceeds MAX_BYTES.
# A path that does not exist counts as empty.
set -euo pipefail

if (($# < 2)); then
  echo "Usage: $0 MAX_BYTES PATH..." >&2
  exit 2
fi

max_bytes="$1"
shift

total=0
for path in "$@"; do
  if [[ -e "$path" ]]; then
    size=$(du -sb "$path" | cut -f1)
  else
    size=0
  fi
  printf '%12d  %s\n' "$size" "$path"
  total=$((total + size))
done
printf '%12d  total (budget %d)\n' "$total" "$max_bytes"

if ((total > max_bytes)); then
  echo "::warning title=Cache over budget::cache paths total ${total} bytes, budget ${max_bytes}; not saving"
  exit 1
fi

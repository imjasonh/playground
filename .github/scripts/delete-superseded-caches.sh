#!/usr/bin/env bash
# Delete the Actions caches that a newly saved cache replaces.
#
# test.yml saves each cache under a key that names the commit, so every save
# adds an entry. GitHub evicts entries by least recent use once the repository
# passes its 10 GB quota, which lets stale entries push out live ones from
# other workflows. After a save, this script leaves one entry for each cache
# family: the one just saved.
#
# Usage:
#   delete-superseded-caches.sh KEEP_KEY PREFIX...
#   delete-superseded-caches.sh "" PREFIX...
#
# With a KEEP_KEY, it deletes entries whose key starts with a PREFIX and that
# were created before KEEP_KEY's entry. It doesn't delete a newer entry, so
# two runs that save at once don't delete each other's entries. When no entry
# has KEEP_KEY, it deletes nothing. With an empty KEEP_KEY, it deletes every
# entry that starts with a PREFIX, which resets a family that grew past its
# budget.
#
# Needs the gh CLI, a token with actions: write in GH_TOKEN, and the
# repository in GH_REPO.
set -euo pipefail

if (($# < 2)); then
  echo "Usage: $0 KEEP_KEY PREFIX..." >&2
  exit 2
fi

keep_key="$1"
shift

keep_created=""
if [[ -n "$keep_key" ]]; then
  keep_created=$(gh cache list --key "$keep_key" --limit 100 --json key,createdAt |
    jq -r --arg key "$keep_key" '[.[] | select(.key == $key)][0].createdAt // empty')
  if [[ -z "$keep_created" ]]; then
    echo "::warning title=Cache not found::no cache has key ${keep_key}; deleting nothing"
    exit 0
  fi
fi

deleted=0
for prefix in "$@"; do
  # An empty prefix matches every cache in the repository.
  [[ -z "$prefix" ]] && continue
  while IFS= read -r line; do
    [[ -z "$line" ]] && continue
    id="${line%%$'\t'*}"
    key="${line#*$'\t'}"
    echo "deleting cache ${key} (${id})"
    gh cache delete "$id"
    deleted=$((deleted + 1))
  done < <(gh cache list --key "$prefix" --limit 100 --json id,key,createdAt |
    jq -r --arg keep "$keep_key" --arg created "$keep_created" --arg prefix "$prefix" \
      '.[] | select((.key | startswith($prefix)) and .key != $keep and ($created == "" or .createdAt < $created)) | "\(.id)\t\(.key)"')
done
echo "deleted ${deleted} cache(s)"

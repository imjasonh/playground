#!/usr/bin/env bash
# Remove orphaned PR preview directories from a published site tree.
#
# Preview deploys write preview/pr-<N>/ under gh-pages (with keep_files: true).
# cleanup.yml removes a single PR's directory on close, but bulk-closing PRs can
# drop webhook deliveries so some closed-PR previews linger — and the production
# home page keeps listing them via preview.json. This script reconciles the
# published preview/ tree against the set of currently open PRs: any
# preview/pr-<N>/ whose number is not open is deleted.
#
# Usage:
#   prune-orphaned-previews.sh <site-dir> [--from-github | <open-pr-number>...]
#
# <site-dir>     Published site to prune (typically a gh-pages checkout).
# --from-github  Query open PR numbers with `gh pr list` (requires gh + auth).
# <numbers...>   Explicit open PR numbers to keep; all other preview/pr-* dirs
#                are removed. Passing no numbers (and not --from-github) means
#                keep none — every preview/pr-* directory is pruned.
set -euo pipefail

site_dir="${1:?site directory required}"
shift

if [[ ! -d "$site_dir" ]]; then
  echo "Site directory not found: $site_dir" >&2
  exit 1
fi

declare -A keep=()

if [[ "${1:-}" == "--from-github" ]]; then
  shift
  if [[ $# -gt 0 ]]; then
    echo "Unexpected arguments after --from-github: $*" >&2
    exit 1
  fi
  if ! command -v gh >/dev/null 2>&1; then
    echo "gh is required for --from-github" >&2
    exit 1
  fi
  while IFS= read -r n; do
    [[ -n "$n" ]] || continue
    keep["$n"]=1
  done < <(gh pr list --state open --limit 1000 --json number --jq '.[].number')
else
  for n in "$@"; do
    if [[ ! "$n" =~ ^[0-9]+$ ]]; then
      echo "Invalid PR number: $n" >&2
      exit 1
    fi
    keep["$n"]=1
  done
fi

preview_root="$site_dir/preview"
if [[ ! -d "$preview_root" ]]; then
  echo "No preview directory; nothing to prune."
  exit 0
fi

pruned=0
for dir in "$preview_root"/*/; do
  [[ -d "$dir" ]] || continue
  name="$(basename "$dir")"
  if [[ ! "$name" =~ ^pr-([0-9]+)$ ]]; then
    continue
  fi
  number="${BASH_REMATCH[1]}"
  if [[ -z "${keep[$number]+x}" ]]; then
    echo "Pruning orphaned preview: $name"
    rm -rf "$dir"
    pruned=$((pruned + 1))
  fi
done

# Drop an empty preview/ directory so the tree stays tidy.
if [[ -d "$preview_root" ]] && [[ -z "$(find "$preview_root" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  rmdir "$preview_root"
  echo "Removed empty preview directory."
fi

if ((pruned == 0)); then
  echo "No orphaned previews to prune."
fi

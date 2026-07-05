#!/usr/bin/env bash
# Regenerate the production root index.html inside a gh-pages working tree and
# push it (together with any already-staged changes, e.g. a removed preview).
#
# Usage:
#   publish-site-index.sh <gh-pages-dir> [repo-url] [commit-message]
#
# The renderer (render-index.py) and template are resolved relative to this
# script — i.e. from the repository checkout — while it scans and commits inside
# <gh-pages-dir>, which is expected to be a checkout of the gh-pages branch.
set -euo pipefail

ghpages_dir="${1:?gh-pages directory required}"
repo_url="${2:-}"
message="${3:-chore: refresh site index}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

python3 "$script_dir/render-index.py" site \
  --dir "$ghpages_dir" \
  --repo-url "$repo_url" \
  --output "$ghpages_dir/index.html"

cd "$ghpages_dir"

git config user.name  "github-actions[bot]"
git config user.email "github-actions[bot]@users.noreply.github.com"

git add -A

if git diff --cached --quiet; then
  echo "Site index unchanged; nothing to publish."
  exit 0
fi

git commit -m "$message"

# Retry push to handle concurrent updates to gh-pages.
for attempt in 1 2 3; do
  if git pull --rebase origin gh-pages && git push; then
    echo "Published site index."
    exit 0
  fi
  echo "Push attempt ${attempt} failed, retrying..."
  sleep 5
done

echo "Failed to publish site index after retries." >&2
exit 1

#!/usr/bin/env bash
# Discover which Cloudflare Worker apps a push changed, for the deploy workflow.
#
# Emits a `workers=<json-array>` line to GITHUB_OUTPUT (and echoes it). On the
# first push to a branch (no prior commit) every Worker app is selected, matching
# the "test everything" behavior of discover-changed-apps.sh.
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
: "${HEAD_SHA:?HEAD_SHA must be set for pushes}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

if [ "$BEFORE_SHA" = "0000000000000000000000000000000000000000" ]; then
  echo "No prior commit; deploying all Worker apps."
  workers=$(bash .github/scripts/discover-worker-apps.sh --all)
else
  changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  if [ -z "$changed" ]; then
    workers='[]'
  else
    workers=$(printf '%s\n' "$changed" | bash .github/scripts/discover-worker-apps.sh --from-changes)
  fi
fi

echo "workers=${workers}" >> "$GITHUB_OUTPUT"
echo "Worker apps to deploy: ${workers}"

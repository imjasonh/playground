#!/usr/bin/env bash
# Discover which Cloudflare Worker apps to deploy, for the deploy workflow.
#
# Emits a `workers=<json-array>` line to GITHUB_OUTPUT (and echoes it). Every
# Worker app is selected when the run was triggered manually (workflow_dispatch)
# or on the first push to a branch (no prior commit, matching the "test
# everything" behavior of discover-changed-apps.sh); otherwise only the Worker
# apps a push changed are selected.
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

if [ "${EVENT_NAME:-}" = "workflow_dispatch" ]; then
  echo "Manual dispatch; deploying all Worker apps."
  workers=$(bash .github/scripts/discover-worker-apps.sh --all)
elif [ "${BEFORE_SHA:-}" = "0000000000000000000000000000000000000000" ]; then
  echo "No prior commit; deploying all Worker apps."
  workers=$(bash .github/scripts/discover-worker-apps.sh --all)
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  if [ -z "$changed" ]; then
    workers='[]'
  else
    workers=$(printf '%s\n' "$changed" | bash .github/scripts/discover-worker-apps.sh --from-changes)
  fi
fi

echo "workers=${workers}" >> "$GITHUB_OUTPUT"
echo "Worker apps to deploy: ${workers}"

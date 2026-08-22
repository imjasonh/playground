#!/usr/bin/env bash
# Discover which exe.dev apps to deploy, for the deploy-exe workflow.
#
# Emits an `apps=<json-array>` line to GITHUB_OUTPUT (and echoes it). Every
# exe app is selected on workflow_dispatch or the first push to a branch;
# otherwise only the exe apps a push changed are selected.
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

if [ "${EVENT_NAME:-}" = "workflow_dispatch" ]; then
  echo "Manual dispatch; deploying all exe.dev apps."
  apps=$(bash .github/scripts/discover-exe-apps.sh --all)
elif [ "${BEFORE_SHA:-}" = "0000000000000000000000000000000000000000" ]; then
  echo "No prior commit; deploying all exe.dev apps."
  apps=$(bash .github/scripts/discover-exe-apps.sh --all)
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  if [ -z "$changed" ]; then
    apps='[]'
  else
    apps=$(printf '%s\n' "$changed" | bash .github/scripts/discover-exe-apps.sh --from-changes)
  fi
fi

echo "apps=${apps}" >> "$GITHUB_OUTPUT"
echo "exe.dev apps to deploy: ${apps}"

#!/usr/bin/env bash
# Discover changed testable browser apps and Go modules for the test workflow.
set -euo pipefail

: "${EVENT_NAME:?EVENT_NAME must be set}"
: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

if [ "$EVENT_NAME" = "pull_request" ]; then
  : "${BASE_REF:?BASE_REF must be set for pull requests}"
  git fetch origin "$BASE_REF"
  changed=$(git diff --name-only "origin/${BASE_REF}...HEAD")
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  if [ "$BEFORE_SHA" = "0000000000000000000000000000000000000000" ]; then
    echo "No prior commit; testing all apps."
    apps=$(bash .github/scripts/discover-testable-apps.sh --all)
    modules=$(bash .github/scripts/discover-go-modules.sh --all)
    {
      echo "apps=${apps}"
      echo "modules=${modules}"
    } >> "$GITHUB_OUTPUT"
    echo "Testable browser apps: ${apps}"
    echo "Go apps: ${modules}"
    exit 0
  else
    changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  fi
fi

if [ -z "$changed" ]; then
  apps='[]'
  modules='[]'
else
  apps=$(printf '%s\n' "$changed" | bash .github/scripts/discover-testable-apps.sh --from-changes)
  modules=$(printf '%s\n' "$changed" | bash .github/scripts/discover-go-modules.sh --from-changes)
fi

{
  echo "apps=${apps}"
  echo "modules=${modules}"
} >> "$GITHUB_OUTPUT"

echo "Changed paths:"
printf '%s\n' "$changed"
echo "Testable browser apps: ${apps}"
echo "Go apps: ${modules}"

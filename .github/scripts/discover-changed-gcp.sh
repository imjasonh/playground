#!/usr/bin/env bash
# Select GCP apps for this workflow run and write apps=<json> to GITHUB_OUTPUT.
#
# Manual runs and the first push deploy every app. Pull requests deploy
# nothing. Other pushes deploy apps whose watch paths changed.
#
# Env: EVENT_NAME, GITHUB_OUTPUT, and for pushes BEFORE_SHA and HEAD_SHA.
# GCP_DEPLOY_ROOT overrides the repo root (tests).
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${EVENT_NAME:?EVENT_NAME must be set}"

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=${GCP_DEPLOY_ROOT:-$(cd "$script_dir/../.." && pwd)}
cd "$repo_root"

if [[ "$EVENT_NAME" == "workflow_dispatch" ]]; then
  echo "Manual dispatch; deploying all GCP apps."
  apps=$(GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --all)
elif [[ "$EVENT_NAME" == "pull_request" ]]; then
  echo "Pull request; not deploying."
  apps='[]'
elif [[ "${BEFORE_SHA:-}" == "0000000000000000000000000000000000000000" ]]; then
  echo "No prior commit; deploying all GCP apps."
  apps=$(GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --all)
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  if [[ -z "$changed" ]]; then
    apps='[]'
  else
    apps=$(printf '%s\n' "$changed" | GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --from-changes)
  fi
fi

echo "apps=${apps}" >>"$GITHUB_OUTPUT"
echo "GCP apps to deploy: ${apps}"

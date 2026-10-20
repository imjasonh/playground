#!/usr/bin/env bash
# Select GCP apps for this workflow run and write apps=<json> to GITHUB_OUTPUT.
#
# Manual runs and the first push select every app. A pull request selects
# the apps its diff would deploy, so the workflow can fail when that app's
# GitHub environment is not configured. The workflow applies only on main.
#
# Env: EVENT_NAME, GITHUB_OUTPUT, and for pushes and pull requests
# BEFORE_SHA and HEAD_SHA. GCP_DEPLOY_ROOT overrides the repo root (tests).
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${EVENT_NAME:?EVENT_NAME must be set}"

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=${GCP_DEPLOY_ROOT:-$(cd "$script_dir/../.." && pwd)}
cd "$repo_root"

# diff_apps REV... prints the JSON array of apps touched by git diff.
diff_apps() {
  local changed
  changed=$(git diff --name-only "$@")
  if [[ -z "$changed" ]]; then
    echo '[]'
    return
  fi
  printf '%s\n' "$changed" | GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --from-changes
}

if [[ "$EVENT_NAME" == "workflow_dispatch" ]]; then
  echo "Manual dispatch; selecting every GCP app."
  apps=$(GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --all)
elif [[ "$EVENT_NAME" == "pull_request" ]]; then
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pull requests}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pull requests}"
  echo "Pull request; selecting changed GCP apps. Apply runs on main."
  apps=$(diff_apps "${BEFORE_SHA}...${HEAD_SHA}")
elif [[ "${BEFORE_SHA:-}" == "0000000000000000000000000000000000000000" ]]; then
  echo "No prior commit; selecting every GCP app."
  apps=$(GCP_DEPLOY_ROOT="$repo_root" bash "$script_dir/discover-gcp-apps.sh" --all)
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  apps=$(diff_apps "$BEFORE_SHA" "$HEAD_SHA")
fi

echo "apps=${apps}" >>"$GITHUB_OUTPUT"
echo "GCP apps to deploy: ${apps}"

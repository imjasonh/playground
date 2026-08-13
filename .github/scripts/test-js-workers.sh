#!/usr/bin/env bash
# Install dependencies and typecheck/test JS/TS Cloudflare Worker apps listed
# in JS_WORKERS as JSON. Same npm ci → npm test path as browser apps; these
# Workers have no index.html so they are not Pages apps.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t apps < <(printf '%s' "${JS_WORKERS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No JS Worker apps changed. Nothing to test."
  exit 0
fi

for app in "${apps[@]}"; do
  echo "::group::Test ${app}"
  (
    cd "$app"
    npm ci
    npm test
  )
  echo "::endgroup::"
done

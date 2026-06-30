#!/usr/bin/env bash
# Install dependencies and test the browser apps listed in APPS as JSON.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t apps < <(printf '%s' "${APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No testable browser apps changed. Nothing to test."
  exit 0
fi

for app in "${apps[@]}"; do
  echo "::group::Test ${app}"
  (
    cd "$app"
    npm ci
    npm test
    if node -e "const s=require('./package.json').scripts||{}; process.exit(s['test:e2e']?0:1)"; then
      npx playwright install --with-deps chromium
      npm run test:e2e
    else
      echo "No test:e2e script; skipping e2e."
    fi
  )
  echo "::endgroup::"
done

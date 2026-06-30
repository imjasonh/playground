#!/usr/bin/env bash
# Update and test every testable top-level JavaScript app.
#
# Writes "result" and "has_changes" step outputs for the dependency workflow.
set -uo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${GITHUB_STEP_SUMMARY:?GITHUB_STEP_SUMMARY must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

result=success
{
  echo
  echo "### Daily JavaScript dependency update"
  echo
} >> "$GITHUB_STEP_SUMMARY"

apps=()
if apps_json=$(bash .github/scripts/discover-testable-apps.sh --all); then
  if app_lines=$(printf '%s' "$apps_json" | jq -r '.[]'); then
    if [ -n "$app_lines" ]; then
      mapfile -t apps <<< "$app_lines"
    fi
  else
    result=failure
    echo "::error title=JavaScript app discovery failed::Discovery returned invalid JSON."
    echo "- ❌ JavaScript app discovery returned invalid JSON." >> "$GITHUB_STEP_SUMMARY"
  fi
else
  result=failure
  echo "::error title=JavaScript app discovery failed::Could not discover testable JavaScript apps."
  echo "- ❌ Could not discover testable JavaScript apps." >> "$GITHUB_STEP_SUMMARY"
fi

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No testable JavaScript apps found."
  if [ "$result" = success ]; then
    echo "- No testable JavaScript apps found." >> "$GITHUB_STEP_SUMMARY"
  fi
fi

for app in "${apps[@]}"; do
  echo "::group::Update and verify ${app}"

  if (
    set -euo pipefail
    cd "$app"
    npx --yes npm-check-updates@latest --upgrade
    npm install
    npm run vendor --if-present
  ); then
    echo "- ✅ \`${app}\`: dependencies updated" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Dependency update failed::${app}: npm dependency update"
    echo "- ❌ \`${app}\`: dependency update failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    set -euo pipefail
    cd "$app"
    npm test
  ); then
    echo "- ✅ \`${app}\`: tests passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Tests failed::${app}: npm test"
    echo "- ❌ \`${app}\`: tests failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$app"
    node -e "const s=require('./package.json').scripts||{}; process.exit(s['test:e2e']?0:1)"
  ); then
    if (
      set -euo pipefail
      cd "$app"
      npx playwright install --with-deps chromium
      npm run test:e2e
    ); then
      echo "- ✅ \`${app}\`: end-to-end tests passed" >> "$GITHUB_STEP_SUMMARY"
    else
      result=failure
      echo "::error title=End-to-end tests failed::${app}: npm run test:e2e"
      echo "- ❌ \`${app}\`: end-to-end tests failed" >> "$GITHUB_STEP_SUMMARY"
    fi
  else
    echo "- \`${app}\`: no end-to-end tests" >> "$GITHUB_STEP_SUMMARY"
  fi

  echo "::endgroup::"
done

if [ -n "$(git status --porcelain -- ':(glob)*/package.json' ':(glob)*/package-lock.json' ':(glob)*/vendor/**')" ]; then
  has_changes=true
else
  has_changes=false
fi

echo "result=${result}" >> "$GITHUB_OUTPUT"
echo "has_changes=${has_changes}" >> "$GITHUB_OUTPUT"

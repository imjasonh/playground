#!/usr/bin/env bash
# Update, build, and test every top-level Go module.
#
# Writes "result" and "has_changes" step outputs for the dependency workflow.
set -uo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${GITHUB_STEP_SUMMARY:?GITHUB_STEP_SUMMARY must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

result=success
{
  echo "### Daily Go dependency update"
  echo
} >> "$GITHUB_STEP_SUMMARY"

modules=()
if modules_json=$(bash .github/scripts/discover-go-modules.sh --all); then
  if module_lines=$(printf '%s' "$modules_json" | jq -r '.[]'); then
    if [ -n "$module_lines" ]; then
      mapfile -t modules <<< "$module_lines"
    fi
  else
    result=failure
    echo "::error title=Go app discovery failed::Discovery returned invalid JSON."
    echo "- ❌ Go app discovery returned invalid JSON." >> "$GITHUB_STEP_SUMMARY"
  fi
else
  result=failure
  echo "::error title=Go app discovery failed::Could not discover Go app modules."
  echo "- ❌ Could not discover Go app modules." >> "$GITHUB_STEP_SUMMARY"
fi

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No Go apps found."
  if [ "$result" = success ]; then
    echo "- No Go apps found." >> "$GITHUB_STEP_SUMMARY"
  fi
fi

for module in "${modules[@]}"; do
  echo "::group::Update and verify ${module}"

  if (
    cd "$module"
    go get -u ./...
  ); then
    echo "- ✅ \`${module}\`: dependencies updated" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Dependency update failed::${module}: go get -u ./..."
    echo "- ❌ \`${module}\`: dependency update failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$module"
    go build ./...
  ); then
    echo "- ✅ \`${module}\`: build passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Build failed::${module}: go build ./..."
    echo "- ❌ \`${module}\`: build failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$module"
    go test ./...
  ); then
    echo "- ✅ \`${module}\`: tests passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Tests failed::${module}: go test ./..."
    echo "- ❌ \`${module}\`: tests failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  echo "::endgroup::"
done

if [ -n "$(git status --porcelain -- ':(glob)*/go.mod' ':(glob)*/go.sum')" ]; then
  has_changes=true
else
  has_changes=false
fi

echo "result=${result}" >> "$GITHUB_OUTPUT"
echo "has_changes=${has_changes}" >> "$GITHUB_OUTPUT"

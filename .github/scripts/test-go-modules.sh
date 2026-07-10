#!/usr/bin/env bash
# Build and test the Go modules listed in MODULES as JSON.
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t modules < <(printf '%s' "${MODULES:-[]}" | jq -r '.[]')

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No Go apps changed. Nothing to test."
  exit 0
fi

result=0
for module in "${modules[@]}"; do
  echo "::group::Build and test ${module}"

  if (
    cd "$module"
    go build ./...
  ); then
    echo "${module}: build passed"
  else
    echo "::error title=Go build failed::${module}: go build ./..."
    result=1
  fi

  # node-image layout conformance tests compare against pnpm; install it when needed.
  if [ "$module" = "node-image" ]; then
    if ! command -v pnpm >/dev/null 2>&1; then
      echo "Installing pnpm for node-image conformance tests"
      npm install -g pnpm@10
    fi
    if ! command -v node >/dev/null 2>&1; then
      echo "::warning title=node missing::node-image conformance tests that need node will skip"
    fi
  fi

  if (
    cd "$module"
    # -v so CI logs show each test (including Docker e2e PASS vs SKIP).
    # node-image Docker-socket e2e builds/runs several images; allow headroom.
    if [ "$module" = "node-image" ]; then
      go test -v -timeout 30m ./...
    else
      go test -v ./...
    fi
  ); then
    echo "${module}: tests passed"
  else
    echo "::error title=Go tests failed::${module}: go test -v ./..."
    result=1
  fi

  echo "::endgroup::"
done

exit "$result"

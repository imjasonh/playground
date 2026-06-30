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

  if [ -d "$module/cmd/wasm" ]; then
    if (
      cd "$module"
      output=$(mktemp)
      trap 'rm -f "$output"' EXIT
      GOOS=js GOARCH=wasm go build -o "$output" ./cmd/wasm
    ); then
      echo "${module}: browser WASM build passed"
    else
      echo "::error title=Go WASM build failed::${module}: GOOS=js GOARCH=wasm go build ./cmd/wasm"
      result=1
    fi
  fi

  if (
    cd "$module"
    go test ./...
  ); then
    echo "${module}: tests passed"
  else
    echo "::error title=Go tests failed::${module}: go test ./..."
    result=1
  fi

  echo "::endgroup::"
done

exit "$result"

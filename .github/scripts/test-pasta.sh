#!/usr/bin/env bash
# Build pasta, run analyzer testdata (`pasta test`), then lint the
# monorepo with the enrolled .pasta/ style rules (-fail-on=warning).
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

if [ ! -d .pasta ]; then
  echo "::error title=pasta::missing .pasta/ project rules directory"
  exit 1
fi

echo "::group::Build pasta"
(
  cd pasta
  go build -o "${RUNNER_TEMP:-/tmp}/pasta-ci" ./cmd/pasta
)
pasta_bin="${RUNNER_TEMP:-/tmp}/pasta-ci"
echo "Built ${pasta_bin}"
echo "::endgroup::"

echo "::group::pasta test (.pasta analyzers)"
"${pasta_bin}" test .pasta
echo "::endgroup::"

echo "::group::pasta lint (./... -fail-on=warning)"
"${pasta_bin}" -fail-on=warning ./...
echo "::endgroup::"

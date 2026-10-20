#!/usr/bin/env bash
# Local checks for pasta.
#
# CI runs the same gofmt checker (.github/scripts/check-gofmt.sh) on
# each changed Go module, then builds and tests with go test -race.
# Run this before sending a PR so a local gofmt failure matches that gate.
#
# When pasta lives inside the playground monorepo, run this from
# pasta/ (or let it locate itself via BASH_SOURCE).

set -euo pipefail

# cd to the pasta module root (directory containing this script's
# ../). Stable whether invoked directly or as a git hook symlink.
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

green() { printf '\033[32m%s\033[0m\n' "$*"; }
step()  { printf '\n\033[1m== %s ==\033[0m\n' "$*"; }

step "gofmt"
# Same checker CI runs. It skips vendor and testdata.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
bash "${repo_root}/.github/scripts/check-gofmt.sh" .

step "go vet"
go vet ./...

step "go build"
go build ./...

# The whole analyzer suite — every analyzers/*/ and testdata/*/
# directory — runs through pasta_test.go's TestAnalyzers /
# TestExtensionDemos. E2E smoke tests (e2e/) shallow-clone real repos;
# pass -short to skip them for a faster local loop.
step "go test"
go test -race ./... -count=1

green "all checks passed"

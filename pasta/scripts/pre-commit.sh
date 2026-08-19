#!/usr/bin/env bash
# pre-commit / CI checks for pasta.
#
# Same script runs on the developer's machine and in local iteration,
# so locally-clean changes can't fail CI on something the hook would
# have caught.
#
# When pasta lives inside the playground monorepo, run this from
# pasta/ (or let it locate itself via BASH_SOURCE).

set -euo pipefail

# cd to the pasta module root (directory containing this script's
# ../). Stable whether invoked directly or as a git hook symlink.
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

red()   { printf '\033[31m%s\033[0m\n' "$*"; }
green() { printf '\033[32m%s\033[0m\n' "$*"; }
step()  { printf '\n\033[1m== %s ==\033[0m\n' "$*"; }

step "gofmt"
unformatted=$(gofmt -l .)
if [ -n "$unformatted" ]; then
  red "gofmt would reformat:"
  echo "$unformatted"
  exit 1
fi

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

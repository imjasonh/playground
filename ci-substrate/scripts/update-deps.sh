#!/usr/bin/env bash
# Updates ci-substrate's Go modules, then moves the ateworker-gvisor image in
# deploy/substrate/workerpool.yaml to the go.ate.dev/substrate release that
# go.mod now requires, so the workers run the release the pool's client is
# built against. update-go-dependencies.sh runs it in place of
# `go get -u ./...`.
#
# Requires go and sed.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

go get -u ./...

version=$(go list -m -f '{{.Version}}' go.ate.dev/substrate)
sed -i -E "s#(ghcr\.io/agent-substrate/substrate/ateworker-gvisor:)[^[:space:]]+#\1${version}#" \
  deploy/substrate/workerpool.yaml

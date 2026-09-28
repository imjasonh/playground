#!/usr/bin/env bash
# Cloud Agent environment install step (see environment.json). Cursor
# runs it when an agent's VM starts, after pulling the latest changes.
#
# Builds pasta from this checkout and installs its git pre-commit hook,
# which runs pasta on the staged files of every agent commit.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

(cd pasta && go install ./cmd/pasta)
bin=$(go env GOBIN)
if [ -z "$bin" ]; then
  bin="$(go env GOPATH)/bin"
fi

# Cursor points core.hooksPath at its own hook dispatcher, which runs
# the repository's .git/hooks/<name> before Cursor's hooks. Install
# pasta's hook there instead of replacing the dispatcher's pre-commit.
hooks="$(cd "$(git rev-parse --git-common-dir)" && pwd)/hooks"
GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=core.hooksPath GIT_CONFIG_VALUE_0="$hooks" \
  "$bin/pasta" install

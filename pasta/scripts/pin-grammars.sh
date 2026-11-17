#!/usr/bin/env bash
# Sets each tree-sitter grammar module in go.mod to the ref that
# internal/tswasm/build.sh compiles into ts-core.wasm, so the cgo and
# wasm backends build the same trees. The daily dependency update runs
# this after `go get -u ./...`; run it after editing build.sh's pins.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

args=()
while read -r _ repo ref _; do
  mod="github.com/${repo}"
  if go list -m "$mod" >/dev/null 2>&1; then
    args+=("${mod}@${ref}")
  fi
done < <(sed -n '/^GRAMMARS=(/,/^)/s/^ *"\(.*\)"$/\1/p' internal/tswasm/build.sh | awk '!seen[$2]++')

if [ "${#args[@]}" -eq 0 ]; then
  echo "pin-grammars: no grammar module from build.sh is in go.mod" >&2
  exit 1
fi
go get "${args[@]}"

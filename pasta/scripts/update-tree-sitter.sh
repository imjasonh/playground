#!/usr/bin/env bash
# Moves the vendored tree-sitter runtime and each grammar in
# internal/tswasm/build.sh to its newest release, and rebuilds
# ts-core.wasm.br when any of them moved. A grammar's newest release is its
# newest tag with the same shape as its current ref, so
# 0.7.3-with-generated-files moves to 0.7.4-with-generated-files and a
# release candidate tag is never picked. The daily dependency update runs
# this before `go get -u ./...` and runs pin-grammars.sh after it.
#
# Requires git and go. A rebuild downloads zig, and the tree-sitter CLI
# that matches the runtime, unless they are already on PATH.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../internal/tswasm"

ZIG_VERSION=0.14.1
VENDOR=csrc/vendor/tree-sitter

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# newest_tag prints the newest tag of GitHub repository $1 that has the
# shape of ref $2, with each run of digits standing for any number.
newest_tag() {
  local shape tags
  shape=$(printf '%s' "$2" | sed -e 's/[][\.*^$+?(){}|]/\\&/g' -e 's/[0-9]\{1,\}/[0-9]+/g')
  tags=$(git ls-remote --tags --refs "https://github.com/$1")
  sed 's|.*refs/tags/||' <<< "$tags" | { grep -E "^${shape}\$" || true; } | sort -V | tail -n 1
}

# newer succeeds when version $2 sorts after version $1.
newer() {
  [ -n "$2" ] && [ "$1" != "$2" ] &&
    [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | tail -n 1)" = "$2" ]
}

changed=0

runtime=$(cat "$VENDOR/VERSION")
latest=$(newest_tag tree-sitter/tree-sitter "$runtime")
if newer "$runtime" "$latest"; then
  echo "tree-sitter runtime: $runtime → $latest"
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$latest" \
    https://github.com/tree-sitter/tree-sitter "$work/runtime"
  rm -rf "$VENDOR"
  mkdir -p "$VENDOR/lib"
  cp "$work/runtime/LICENSE" "$VENDOR/"
  cp -R "$work/runtime/lib/include" "$work/runtime/lib/src" "$VENDOR/lib/"
  # The wasm store needs wasmtime, which pasta doesn't link.
  rm -rf "$VENDOR/lib/src/wasm" "$VENDOR/lib/src/wasm-stdlib"
  echo "$latest" > "$VENDOR/VERSION"
  runtime=$latest
  changed=1
fi

while read -r repo ref; do
  latest=$(newest_tag "$repo" "$ref")
  if newer "$ref" "$latest"; then
    echo "$repo: $ref → $latest"
    sed -i -E "s#^( *\"[a-z]+ +${repo//./\\.} +)${ref//./\\.} #\1${latest} #" build.sh
    changed=1
  fi
done < <(sed -n '/^GRAMMARS=(/,/^)/s/^ *"\(.*\)"$/\1/p' build.sh | awk '!seen[$2]++ { print $2, $3 }')

if [ "$changed" = 0 ]; then
  echo "tree-sitter runtime and grammars are current"
  exit 0
fi

if ! command -v zig > /dev/null 2>&1; then
  zig_dir="zig-$(uname -m)-linux-${ZIG_VERSION}"
  curl -fsSL "https://ziglang.org/download/${ZIG_VERSION}/${zig_dir}.tar.xz" | tar -xJ -C "$work"
  PATH="$work/$zig_dir:$PATH"
fi
# Grammars that build.sh generates get the parser ABI of this CLI, so it
# matches the runtime.
if ! tree-sitter --version 2> /dev/null | grep -qF " ${runtime#v}"; then
  npm install --silent --prefix "$work/cli" "tree-sitter-cli@${runtime#v}"
  PATH="$work/cli/node_modules/.bin:$PATH"
fi
bash build.sh

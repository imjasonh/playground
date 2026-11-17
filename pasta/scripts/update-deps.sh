#!/usr/bin/env bash
# Updates pasta's Go modules, the vendored tree-sitter runtime, and the git
# grammars in internal/tswasm/grammars.txt, then rebuilds ts-core.wasm.br if
# the runtime or any grammar moved. update-go-dependencies.sh runs it in
# place of `go get -u ./...`.
#
# Requires git, go, curl, and npm.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

TSWASM=internal/tswasm
VENDOR=$TSWASM/csrc/vendor/tree-sitter
GRAMMARS=$TSWASM/grammars.txt

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# newest_tag prints the newest tag of GitHub repository $1 that has the shape
# of tag $2, with each run of digits standing for any number: v0.3.11 matches
# v0.4.0 and not v0.4.0-rc1.
newest_tag() {
  local shape tags
  shape=$(printf '%s' "$2" | sed -e 's/[][\.*^$+?(){}|]/\\&/g' -e 's/[0-9]\{1,\}/[0-9]+/g')
  tags=$(git ls-remote --tags --refs "https://github.com/$1")
  sed 's|.*refs/tags/||' <<< "$tags" | { grep -E "^${shape}\$" || true; } | sort -V | tail -n 1
}

newer() {
  [ -n "$2" ] && [ "$1" != "$2" ] &&
    [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | tail -n 1)" = "$2" ]
}

grammar_versions() {
  awk '!/^#/ && $4 == "go.mod" { print "github.com/" $2 }' "$GRAMMARS" | sort -u | xargs go list -m
}

before=$(grammar_versions)
# Swift tags its releases without a v, so `go get -u` alone would move it to
# its default branch, which doesn't commit the generated parser.
swift=$(newest_tag alex-pinkus/tree-sitter-swift 0.0.0-with-generated-files)
go get -u ./... "github.com/alex-pinkus/tree-sitter-swift@$swift"
changed=0
if [ "$(grammar_versions)" != "$before" ]; then
  changed=1
fi

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
  # Only compiled with TREE_SITTER_FEATURE_WASM, which needs wasmtime.
  rm -rf "$VENDOR/lib/src/wasm" "$VENDOR/lib/src/wasm-stdlib"
  echo "$latest" > "$VENDOR/VERSION"
  changed=1
fi

while read -r id repo ref; do
  latest=$(newest_tag "$repo" "$ref")
  if newer "$ref" "$latest"; then
    echo "$id: $ref → $latest"
    awk -v id="$id" -v ref="$latest" '$1 == id { sub(/[^ ]+$/, ref) } 1' "$GRAMMARS" > "$work/grammars.txt"
    mv "$work/grammars.txt" "$GRAMMARS"
    changed=1
  fi
done < <(awk '!/^#/ && NF && $4 != "go.mod" { print $1, $2, $4 }' "$GRAMMARS")

if [ "$changed" = 1 ]; then
  bash "$TSWASM/build.sh"
fi

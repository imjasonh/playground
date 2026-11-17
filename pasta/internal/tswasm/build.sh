#!/usr/bin/env bash
# Builds ts-core.wasm.br from the tree-sitter runtime in csrc/vendor, the
# grammars in grammars.txt, and csrc/host_extra.c, as one wasm32-wasi reactor.
#
# Requires git, go, and npm. Zig comes from .github/scripts/install-zig.sh,
# which downloads it on Linux x86_64 and needs it on PATH elsewhere.
set -euo pipefail
cd "$(dirname "$0")"

TS=csrc/vendor/tree-sitter
CLI_VERSION=$(sed 's/^v//' "$TS/VERSION")
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
PATH="$(bash ../../../.github/scripts/install-zig.sh | tail -n 1):$PATH"

SRCS=("$TS/lib/src/lib.c" csrc/host_extra.c)
INCS=(-I "$TS/lib/include" -I "$TS/lib/src")
EXPORTS=()

while read -r id repo sub ref; do
  if [ "$ref" = go.mod ]; then
    go mod download "github.com/$repo"
    read -r dir ref < <(go list -m -f '{{.Dir}} {{.Version}}' "github.com/$repo")
  else
    dir="$WORK/$id"
    git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$ref" \
      "https://github.com/$repo" "$dir"
  fi
  src="$dir/$sub"
  if [ ! -f "$src/parser.c" ]; then
    # The generated parser has the CLI's ABI, which must match the runtime's.
    (cd "$dir" && npm exec --yes --package="tree-sitter-cli@$CLI_VERSION" -- tree-sitter generate)
  fi
  echo "  $id: $repo@$ref"
  SRCS+=("$src/parser.c")
  if [ -f "$src/scanner.c" ]; then
    SRCS+=("$src/scanner.c")
  fi
  INCS+=(-I "$src")
  EXPORTS+=("-Wl,--export=tree_sitter_$id")
done < <(grep -Ev '^(#|$)' grammars.txt)

zig cc --target=wasm32-wasi-musl -mexec-model=reactor \
  "${INCS[@]}" "${SRCS[@]}" \
  -o ts-core.wasm -Oz -fPIC -Wl,--no-entry -Wl,--strip-debug \
  -Wl,--export=malloc -Wl,--export=free \
  -Wl,--export=ts_parser_new -Wl,--export=ts_parser_delete \
  -Wl,--export=ts_parser_set_language -Wl,--export=pasta_parse \
  -Wl,--export=ts_parser_reset \
  -Wl,--export=ts_tree_delete \
  -Wl,--export=ts_dump_tree -Wl,--export=ts_dump_rec_size \
  -Wl,--export=ts_language_symbol_count -Wl,--export=ts_language_symbol_name \
  -Wl,--export=ts_language_field_count -Wl,--export=ts_language_field_name_for_id \
  "${EXPORTS[@]}"
go run compress.go

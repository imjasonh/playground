#!/usr/bin/env bash
# Builds ts-core.wasm: official tree-sitter C runtime + pasta's grammars +
# csrc/host_extra.c (batched ts_dump_tree), as one wasm32-wasi reactor via zig cc.
#
# Prior art: dvcdsys/code-index server/internal/chunker/tswasm/build.sh
#
# Requires: zig, git. Optional: tree-sitter CLI for grammars that need generate.
#
# Output: ts-core.wasm (gitignored) and ts-core.wasm.br (committed, go:embed).
set -euo pipefail
cd "$(dirname "$0")"

TS_VERSION="${TS_VERSION:-v0.25.10}"
OUT="${OUT:-ts-core.wasm}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# id repo ref srcsubdir [gen]
# Keep in sync with internal/lang/grammars.go (+ tsx for JSX-in-TS).
GRAMMARS=(
  "go           tree-sitter/tree-sitter-go           v0.25.0  src"
  "python       tree-sitter/tree-sitter-python       v0.25.0  src"
  "rust         tree-sitter/tree-sitter-rust         v0.24.2  src"
  "javascript   tree-sitter/tree-sitter-javascript   v0.25.0  src"
  "typescript   tree-sitter/tree-sitter-typescript   v0.23.2  typescript/src"
  "tsx          tree-sitter/tree-sitter-typescript   v0.23.2  tsx/src"
  "yaml         tree-sitter-grammars/tree-sitter-yaml v0.7.1  src"
  "bash         tree-sitter/tree-sitter-bash         v0.25.1  src"
  "json         tree-sitter/tree-sitter-json         v0.24.8  src"
  "c            tree-sitter/tree-sitter-c            v0.24.2  src"
  "cpp          tree-sitter/tree-sitter-cpp          v0.23.4  src"
  "css          tree-sitter/tree-sitter-css          v0.25.0  src"
  "dockerfile   camdencheek/tree-sitter-dockerfile   v0.2.0   src"
  "html         tree-sitter/tree-sitter-html         v0.23.2  src"
  "java         tree-sitter/tree-sitter-java         v0.23.5  src"
  "php          tree-sitter/tree-sitter-php          v0.24.2  php/src"
  "ruby         tree-sitter/tree-sitter-ruby         v0.23.1  src"
  "sql          DerekStride/tree-sitter-sql          v0.3.11  src 1"
  "swift        alex-pinkus/tree-sitter-swift        0.7.3-with-generated-files src"
)

clone() {
  local repo="$1" ref="$2" dest="$3"
  git clone --depth 1 --branch "$ref" "https://github.com/$repo" "$dest" >/dev/null 2>&1 && return 0
  git clone "https://github.com/$repo" "$dest" >/dev/null 2>&1 || return 1
  git -C "$dest" checkout "$ref" >/dev/null 2>&1
}

echo "→ tree-sitter runtime $TS_VERSION"
git clone --depth 1 --branch "$TS_VERSION" https://github.com/tree-sitter/tree-sitter "$WORK/tree-sitter" 2>/dev/null

SRCS=( "$WORK/tree-sitter/lib/src/lib.c" "csrc/host_extra.c" )
INCS=( -I "$WORK/tree-sitter/lib/include" -I "$WORK/tree-sitter/lib/src" )
EXPORTS=()
BUILT=()
FAILED=()

# typescript and tsx share one clone
declare -A CLONED=()

for row in "${GRAMMARS[@]}"; do
  read -r id repo ref sub gen <<<"$row"
  printf '  %-12s %s@%s  ' "$id" "$repo" "$ref"
  dest="$WORK/$id"
  # Reuse typescript clone for tsx
  if [ "$id" = "tsx" ] && [ -n "${CLONED[tree-sitter/tree-sitter-typescript]:-}" ]; then
    dest="${CLONED[tree-sitter/tree-sitter-typescript]}"
  elif [ -n "${CLONED[$repo]:-}" ]; then
    dest="${CLONED[$repo]}"
  else
    if ! clone "$repo" "$ref" "$dest"; then
      echo "CLONE FAIL"
      FAILED+=("$id")
      continue
    fi
    CLONED[$repo]="$dest"
  fi
  gsrc="$dest/$sub"
  if [ "${gen:-0}" = "1" ] && [ ! -f "$gsrc/parser.c" ]; then
    if command -v tree-sitter >/dev/null 2>&1; then
      ( cd "$dest" && tree-sitter generate >/dev/null 2>&1 ) || true
    fi
  fi
  if [ ! -f "$gsrc/parser.c" ]; then
    echo "NO parser.c"
    FAILED+=("$id")
    continue
  fi
  SRCS+=( "$gsrc/parser.c" )
  [ -f "$gsrc/scanner.c" ] && SRCS+=( "$gsrc/scanner.c" )
  [ -f "$gsrc/scanner.cc" ] && SRCS+=( "$gsrc/scanner.cc" )
  INCS+=( -I "$gsrc" )
  EXPORTS+=( -Wl,--export=tree_sitter_$id )
  BUILT+=("$id")
  echo "ok"
done

echo "→ compiling ${#SRCS[@]} sources, ${#BUILT[@]} grammars → $OUT"
zig cc --target=wasm32-wasi-musl -mexec-model=reactor \
  "${INCS[@]}" "${SRCS[@]}" \
  -o "$OUT" -Oz -fPIC -Wl,--no-entry -Wl,--strip-debug \
  -Wl,--export=malloc -Wl,--export=free \
  -Wl,--export=ts_parser_new -Wl,--export=ts_parser_delete \
  -Wl,--export=ts_parser_set_language -Wl,--export=ts_parser_parse_string \
  -Wl,--export=ts_parser_reset \
  -Wl,--export=ts_parser_set_timeout_micros \
  -Wl,--export=ts_parser_set_cancellation_flag \
  -Wl,--export=ts_tree_delete -Wl,--export=ts_tree_root_node \
  -Wl,--export=ts_dump_tree -Wl,--export=ts_dump_rec_size \
  -Wl,--export=ts_language_symbol_count -Wl,--export=ts_language_symbol_name \
  -Wl,--export=ts_language_field_count -Wl,--export=ts_language_field_name_for_id \
  "${EXPORTS[@]}"

echo "built $OUT ($(du -h "$OUT" | cut -f1)) — runtime $TS_VERSION, ${#BUILT[@]} grammars"
[ ${#FAILED[@]} -gt 0 ] && echo "FAILED: ${FAILED[*]}" && exit 1
echo "grammars: ${BUILT[*]}"

echo "→ brotli-compressing → ${OUT}.br"
GOTOOLCHAIN="${GOTOOLCHAIN:-go1.25.0}" go run compress.go

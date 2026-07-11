#!/usr/bin/env bash
# End-to-end test of the git server over real HTTP, with a real `git` client.
#
# Two modes:
#
#   ./scripts/e2e.sh              # local: builds the Worker (wasm) and runs it
#                                 # under `wrangler dev` (workerd/miniflare with
#                                 # local R2 + Durable Object + KV simulators)
#   GIT_SERVER_URL=https://... ./scripts/e2e.sh
#                                 # remote: same test suite against an already
#                                 # deployed backend (no build, no wrangler)
#
# Requirements (local mode): node/npx (wrangler is fetched via npx), the Rust
# wasm32 target, and worker-build (`cargo +stable install worker-build@0.8.5`).
#
# The test pushes to a uniquely named repo, clones it back, verifies contents
# and `git fsck`, exercises incremental push/pull, the file/tree/blame APIs,
# and repack — a smoke test of the full wasm + Workers-runtime + storage
# stack. It intentionally covers only the core lifecycle; the exhaustive
# suite (shallow/partial clone, races, error paths, memory budgets) is
# `cargo test` (tests/integration.rs, tests/memory.rs), which runs the same
# handler code natively.

set -euo pipefail
cd "$(dirname "$0")/.."

WRANGLER_PID=""
TMP="$(mktemp -d)"
cleanup() {
  [ -n "$WRANGLER_PID" ] && kill "$WRANGLER_PID" 2>/dev/null || true
  rm -rf "$TMP"
}
trap cleanup EXIT

if [ -z "${GIT_SERVER_URL:-}" ]; then
  echo "==> building Worker and starting wrangler dev (local workerd)"
  PORT="${PORT:-8787}"
  # `wrangler dev` runs the [build] command from wrangler.toml itself, but we
  # pre-build to fail fast with a readable error if the wasm build breaks.
  worker-build --release >/dev/null

  npx -y wrangler@4 dev --port "$PORT" --local >"$TMP/wrangler.log" 2>&1 &
  WRANGLER_PID=$!
  GIT_SERVER_URL="http://127.0.0.1:$PORT"

  echo "==> waiting for wrangler dev to become ready"
  for i in $(seq 1 60); do
    if curl -fsS "$GIT_SERVER_URL/" >/dev/null 2>&1; then break; fi
    if ! kill -0 "$WRANGLER_PID" 2>/dev/null; then
      echo "wrangler dev exited early:"; tail -50 "$TMP/wrangler.log"; exit 1
    fi
    sleep 1
    [ "$i" = 60 ] && { echo "wrangler dev never became ready"; tail -50 "$TMP/wrangler.log"; exit 1; }
  done
fi

REPO="e2e-$(date +%s)-$RANDOM"
URL="$GIT_SERVER_URL/$REPO"
echo "==> testing against $URL"

export GIT_AUTHOR_NAME="E2E" GIT_AUTHOR_EMAIL="e2e@example.com"
export GIT_COMMITTER_NAME="E2E" GIT_COMMITTER_EMAIL="e2e@example.com"
export GIT_CONFIG_NOSYSTEM=1 HOME="$TMP"

fail() { echo "FAIL: $1" >&2; exit 1; }

# --- 1. push a new repo ------------------------------------------------------
SRC="$TMP/src"
mkdir -p "$SRC"
git -C "$SRC" init -q -b main .
printf '# hello\n\nworld\n' > "$SRC/README.md"
mkdir -p "$SRC/src"
printf 'fn one() {}\nfn two() {}\n' > "$SRC/src/lib.rs"
git -C "$SRC" add .
git -C "$SRC" commit -q -m "initial commit"
git -C "$SRC" remote add origin "$URL"
git -C "$SRC" push -q origin main || fail "initial push"
echo "ok: push"

# --- 2. clone it back --------------------------------------------------------
git clone -q "$URL" "$TMP/clone" || fail "clone"
diff -u "$SRC/README.md" "$TMP/clone/README.md" || fail "cloned content"
git -C "$TMP/clone" fsck --strict || fail "fsck after clone"
echo "ok: clone + fsck"

# --- 3. incremental push + pull ----------------------------------------------
printf 'fn one() {}\nfn two() {}\nfn three() {}\n' > "$SRC/src/lib.rs"
git -C "$SRC" add .
git -C "$SRC" commit -q -m "add three"
git -C "$SRC" push -q origin main || fail "incremental push"
git -C "$TMP/clone" pull -q origin main || fail "incremental pull"
grep -q three "$TMP/clone/src/lib.rs" || fail "pulled content"
echo "ok: incremental push + pull"

# --- 4. read APIs --------------------------------------------------------------
api() { curl -fsS "$GIT_SERVER_URL/api/$REPO/$1"; }

api "file/main/src/lib.rs" | grep -q "fn three" || fail "file API"
api "tree/main/src" | grep -q '"lib.rs"' || fail "tree API"
api "tree/main/src" | grep -q '"last_commit"' || fail "tree API last_commit"
api "blame/main/src/lib.rs" | grep -q '"commit"' || fail "blame API"
HEAD_OID=$(git -C "$SRC" rev-parse HEAD)
api "refs" | grep -q "$HEAD_OID" || fail "refs API"
# Blame line 3 must be attributed to the second commit.
api "blame/main/src/lib.rs" | grep -q "$HEAD_OID" || fail "blame attribution"
echo "ok: file/tree/blame/refs APIs"

# --- 5. repack, then verify again ---------------------------------------------
curl -fsS -X POST "$GIT_SERVER_URL/api/$REPO/repack" | grep -q "Repacked" || fail "repack"
git clone -q "$URL" "$TMP/clone2" || fail "clone after repack"
git -C "$TMP/clone2" fsck --strict || fail "fsck after repack"
api "blame/main/src/lib.rs" | grep -q "$HEAD_OID" || fail "blame after repack"
echo "ok: repack + re-clone + blame"

echo
echo "ALL E2E CHECKS PASSED against $GIT_SERVER_URL"

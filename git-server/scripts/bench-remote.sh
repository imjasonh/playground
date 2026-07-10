#!/usr/bin/env bash
# Benchmark a running git-server backend — deployed or local — and report
# latency, throughput, and per-operation cost as measured *by the server
# itself* (via the Server-Timing header every response carries).
#
#   GIT_SERVER_URL=https://git.<account>.workers.dev ./scripts/bench-remote.sh
#   ./scripts/bench-remote.sh          # no URL: builds + runs wrangler dev --local
#
# Tunables:
#   BENCH_MB=64        bulk incompressible payload in the initial push (MiB)
#   BENCH_FILES=300    tracked text files
#   BENCH_COMMITS=30   history depth (each touches ~3 files)
#   BENCH_API_ITERS=5  timed iterations per API endpoint
#
# Use this after deploying to validate the cost model in docs/design.md:
# the op counts (r2a/r2b/do/kv) and µ$ figures come from the server's own
# counters, so they are exact regardless of where it runs; latency and
# throughput include real network + R2 for remote runs.
#
# For the git-protocol endpoints (push/clone), per-request server metrics are
# in the Workers logs — run `npx wrangler tail --format json` in another
# terminal and look for {"evt":"req",...} lines with phase breakdowns.

set -euo pipefail
cd "$(dirname "$0")/.."

BENCH_MB="${BENCH_MB:-64}"
BENCH_FILES="${BENCH_FILES:-300}"
BENCH_COMMITS="${BENCH_COMMITS:-30}"
BENCH_API_ITERS="${BENCH_API_ITERS:-5}"

WRANGLER_PID=""
TMP="$(mktemp -d)"
cleanup() {
  [ -n "$WRANGLER_PID" ] && kill "$WRANGLER_PID" 2>/dev/null || true
  rm -rf "$TMP"
}
trap cleanup EXIT

if [ -z "${GIT_SERVER_URL:-}" ]; then
  echo "==> no GIT_SERVER_URL; building Worker and starting wrangler dev (local workerd)"
  PORT="${PORT:-8787}"
  worker-build --release >/dev/null
  npx -y wrangler@4 dev --port "$PORT" --local >"$TMP/wrangler.log" 2>&1 &
  WRANGLER_PID=$!
  GIT_SERVER_URL="http://127.0.0.1:$PORT"
  for i in $(seq 1 60); do
    curl -fsS "$GIT_SERVER_URL/" >/dev/null 2>&1 && break
    kill -0 "$WRANGLER_PID" 2>/dev/null || { tail -30 "$TMP/wrangler.log"; exit 1; }
    sleep 1
    [ "$i" = 60 ] && { echo "wrangler dev never became ready"; exit 1; }
  done
fi

REPO="bench-$(date +%s)-$RANDOM"
URL="$GIT_SERVER_URL/$REPO"
echo "==> benchmarking $URL"
echo "    shape: ${BENCH_MB} MiB bulk + ${BENCH_FILES} files x ${BENCH_COMMITS} commits"
echo

export GIT_AUTHOR_NAME="Bench" GIT_AUTHOR_EMAIL="bench@example.com"
export GIT_COMMITTER_NAME="Bench" GIT_COMMITTER_EMAIL="bench@example.com"
export GIT_CONFIG_NOSYSTEM=1 HOME="$TMP"

now_ms() { date +%s%3N; }

# --- Build the synthetic repo -------------------------------------------------
SRC="$TMP/src"
mkdir -p "$SRC"
git -C "$SRC" init -q -b main .
for f in $(seq 1 "$BENCH_FILES"); do
  d="$SRC/dir$((f % 20))"
  mkdir -p "$d"
  for l in $(seq 1 30); do echo "file $f line $l"; done > "$d/file$f.txt"
done
head -c "$((BENCH_MB * 1024 * 1024))" /dev/urandom > "$SRC/bulk.bin"
git -C "$SRC" add .
git -C "$SRC" commit -q -m "initial import"
for c in $(seq 2 "$BENCH_COMMITS"); do
  for f in $((c % BENCH_FILES + 1)) $(((c * 7) % BENCH_FILES + 1)) $(((c * 13) % BENCH_FILES + 1)); do
    echo "edit in commit $c" >> "$SRC/dir$((f % 20))/file$f.txt"
  done
  git -C "$SRC" add .
  git -C "$SRC" commit -q -m "commit $c"
done
git -C "$SRC" remote add origin "$URL"

# Bytes git will actually send (its own pack of the whole history).
PACK_BYTES=$(git -C "$SRC" rev-list --objects --all | git -C "$SRC" pack-objects --stdout -q | wc -c)
mib() { awk -v b="$1" 'BEGIN { printf "%.1f", b / 1048576 }'; }
gibps() { awk -v b="$1" -v ms="$2" 'BEGIN { printf "%.3f", b / 1073741824 / (ms / 1000) }'; }

# --- Bulk transfer ------------------------------------------------------------
echo "== bulk transfer =="
t0=$(now_ms); git -C "$SRC" push -q origin main; t1=$(now_ms)
echo "push  (full, $(mib "$PACK_BYTES") MiB): $((t1 - t0)) ms  ->  $(gibps "$PACK_BYTES" $((t1 - t0))) GiB/s"

t0=$(now_ms); git clone -q "$URL" "$TMP/clone"; t1=$(now_ms)
echo "clone (full, $(mib "$PACK_BYTES") MiB): $((t1 - t0)) ms  ->  $(gibps "$PACK_BYTES" $((t1 - t0))) GiB/s"

echo "edit" >> "$SRC/dir1/file1.txt"
git -C "$SRC" add . && git -C "$SRC" commit -q -m "inc"
t0=$(now_ms); git -C "$SRC" push -q origin main; t1=$(now_ms)
echo "push  (incremental):        $((t1 - t0)) ms"
t0=$(now_ms); git -C "$TMP/clone" pull -q origin main; t1=$(now_ms)
echo "pull  (incremental):        $((t1 - t0)) ms"
echo

# --- API latency + server-reported cost ---------------------------------------
# Each row: median client latency over N runs, plus the server's own numbers
# parsed from the Server-Timing header (total/backend ms, op counts, µ$).
api_bench() {
  local name="$1" url="$2"
  local times=() headers="$TMP/h.txt"
  for _ in $(seq 1 "$BENCH_API_ITERS"); do
    local t
    t=$(curl -fsS -o /dev/null -D "$headers" -w '%{time_total}' "$url") \
      || { echo "$name: request failed"; return 1; }
    times+=("$t")
  done
  local median
  median=$(printf '%s\n' "${times[@]}" | sort -n | awk '{a[NR]=$1} END {printf "%.1f", a[int((NR+1)/2)]*1000}')
  local st
  st=$(tr -d '\r' < "$headers" | grep -i '^server-timing:' | cut -d' ' -f2- || true)
  local total backend r2a r2b do_ kv cost
  total=$(sed -n 's/.*total;dur=\([0-9.]*\).*/\1/p' <<<"$st")
  backend=$(sed -n 's/.*backend;dur=\([0-9.]*\).*/\1/p' <<<"$st")
  r2a=$(sed -n 's/.*r2a;desc="\([0-9]*\)".*/\1/p' <<<"$st")
  r2b=$(sed -n 's/.*r2b;desc="\([0-9]*\)".*/\1/p' <<<"$st")
  do_=$(sed -n 's/.*do;desc="\([0-9]*\)".*/\1/p' <<<"$st")
  kv=$(sed -n 's/.*kv;desc="\([0-9]*\)".*/\1/p' <<<"$st")
  cost=$(sed -n 's/.*cost;desc="\([0-9.]*\)u\$".*/\1/p' <<<"$st")
  printf '%-28s %8s ms %9s ms %9s ms %4s %4s %3s %3s %9sµ$\n' \
    "$name" "$median" "${total:-?}" "${backend:-?}" "${r2a:-?}" "${r2b:-?}" "${do_:-?}" "${kv:-?}" "${cost:-?}"
}

run_apis() {
  printf '%-28s %11s %12s %12s %4s %4s %3s %3s %10s\n' \
    "endpoint" "client-med" "srv-total" "srv-backend" "r2a" "r2b" "do" "kv" "cost"
  api_bench "refs"        "$GIT_SERVER_URL/api/$REPO/refs"
  api_bench "file (text)" "$GIT_SERVER_URL/api/$REPO/file/main/dir1/file1.txt"
  api_bench "file (bulk)" "$GIT_SERVER_URL/api/$REPO/file/main/bulk.bin"
  api_bench "tree"        "$GIT_SERVER_URL/api/$REPO/tree/main/dir1"
  api_bench "blame"       "$GIT_SERVER_URL/api/$REPO/blame/main/dir1/file1.txt"
}

echo "== read APIs (before repack: $((BENCH_COMMITS + 1)) push segments) =="
run_apis
echo

echo "== repack =="
t0=$(now_ms)
curl -fsS -X POST -D "$TMP/h.txt" "$GIT_SERVER_URL/api/$REPO/repack"; echo
t1=$(now_ms)
echo "repack: $((t1 - t0)) ms;  $(tr -d '\r' < "$TMP/h.txt" | grep -i '^server-timing:' | cut -d' ' -f2-)"
echo

echo "== read APIs (after repack: 1 pack, sharded filelog) =="
run_apis
echo

echo "NOTE: benchmark repo '$REPO' remains on the server (there is no delete"
echo "API yet); server-side per-request logs for the git-protocol endpoints"
echo "are visible with: npx wrangler tail --format json"
echo
echo "BENCHMARK COMPLETE against $GIT_SERVER_URL"

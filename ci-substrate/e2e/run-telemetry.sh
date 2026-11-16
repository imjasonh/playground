#!/usr/bin/env bash
# Build e2e/bazel with stock Bazel and fail unless the build shows up in the
# telemetry: one trace per Bazel invocation in Jaeger, with spans from cas
# and the runner under the invocation's root span, read totals on each
# runner.execute span and no span per blob read, the build's metrics on the
# collector's Prometheus endpoint, and cas's summary log line.
# run-kind.sh runs it after run-bazel.sh, with port-forwards to cas, Jaeger's
# query API, and the collector's Prometheus endpoint:
#
#   bash e2e/run-telemetry.sh 127.0.0.1:18980 127.0.0.1:16686 127.0.0.1:18889
#
# The trace ID is a function of Bazel's invocation ID, so the script finds
# the trace without searching. cas emits the root span once the invocation
# has been quiet for INVOCATION_IDLE (one minute by default), so the wait is
# longer than that.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAS_ADDR="${1:?usage: run-telemetry.sh <cas host:port> <jaeger host:port> <prometheus host:port>}"
JAEGER_ADDR="${2:?usage: run-telemetry.sh <cas host:port> <jaeger host:port> <prometheus host:port>}"
PROM_ADDR="${3:?usage: run-telemetry.sh <cas host:port> <jaeger host:port> <prometheus host:port>}"
BAZEL_VERSION="$(cat "${ROOT}/e2e/bazel/.bazelversion")"
WAIT_SECONDS="${CI_SUBSTRATE_TELEMETRY_WAIT:-180}"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/ci-substrate-telemetry-XXXXXX")"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# shellcheck source=lib-bazel.sh
source "${ROOT}/e2e/lib-bazel.sh"

BAZEL="${CI_SUBSTRATE_BAZEL:-$(install_bazel "${BAZEL_VERSION}")}"

cleanup() {
  if [[ -d "${WORKDIR}/ws" ]]; then
    (cd "${WORKDIR}/ws" && "${BAZEL}" --output_user_root="${WORKDIR}/root" shutdown) >/dev/null 2>&1 || true
  fi
  chmod -R u+w "${WORKDIR}" 2>/dev/null || true
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

mkdir -p "${WORKDIR}/ws"
cp -R "${ROOT}/e2e/bazel/." "${WORKDIR}/ws/"
echo "telemetry-$(date +%s)-${RANDOM}${RANDOM}" >"${WORKDIR}/ws/salt.txt"
INVOCATION_ID="$(python3 -c 'import uuid; print(uuid.uuid4())')"
TRACE_ID="$(printf '%s' "ci-substrate/invocation/${INVOCATION_ID}" | sha256sum | cut -c1-32)"

echo "==> Building //:fanout as invocation ${INVOCATION_ID} (trace ${TRACE_ID})"
(
  cd "${WORKDIR}/ws"
  "${BAZEL}" --output_user_root="${WORKDIR}/root" build //:fanout \
    --invocation_id="${INVOCATION_ID}" \
    --remote_executor="grpc://${CAS_ADDR}" --spawn_strategy=remote \
    --remote_instance_name=tenant-a \
    --remote_header=x-ci-substrate-tenant=tok-a \
    --remote_timeout=120 --jobs=32 --color=no --curses=no
) >"${WORKDIR}/build.log" 2>&1 || {
  cat "${WORKDIR}/build.log" >&2
  fail "bazel build"
}
grep -E '^INFO: [0-9]+ process(es)?: ' "${WORKDIR}/build.log" | tail -1

# check_trace prints what the trace still lacks, or nothing when it is whole.
check_trace() {
  { curl -fsS "http://${JAEGER_ADDR}/api/traces/${TRACE_ID}" 2>/dev/null || true; } | python3 -c '
import json, sys
try:
    data = json.load(sys.stdin)["data"]
except Exception:
    print("no trace yet")
    sys.exit()
spans = [s for t in data for s in t["spans"]]
procs = {k: v["serviceName"] for t in data for k, v in t["processes"].items()}
services = {procs[s["processID"]] for s in spans}
names = {s["operationName"] for s in spans}
missing = [f"service {s}" for s in ("cas", "runner") if s not in services]
missing += [f"span {n!r}" for n in ("bazel invocation", "scheduler.queue", "runner.execute", "runner.run") if n not in names]
executes = [s for s in spans if s["operationName"] == "runner.execute"]
if executes and not all(any(t["key"] == "ci_substrate.reads.prepare.blobs" for t in s["tags"]) for s in executes):
    missing.append("ci_substrate.reads.prepare.blobs on every runner.execute")
reads = [n for n in names if n.endswith("/BatchReadBlobs") or n.endswith("/Read")]
if reads:
    print(f"FATAL: blob read spans {reads} were sampled")
elif missing:
    print(", ".join(missing))
else:
    print(f"{len(spans)} spans from {sorted(services)}", file=sys.stderr)
'
}

echo "==> Waiting for the trace in Jaeger"
deadline=$((SECONDS + WAIT_SECONDS))
while :; do
  missing="$(check_trace)"
  [[ -z "${missing}" ]] && break
  [[ "${missing}" == FATAL:* ]] && fail "trace ${TRACE_ID}: ${missing#FATAL: }"
  ((SECONDS < deadline)) || fail "trace ${TRACE_ID} lacks ${missing}"
  sleep 5
done

echo "==> Checking metrics on the collector"
# The root span and the invocation metrics are emitted together, so by now
# the next export has them or is at most one interval away.
want=(cas_blob_bytes cas_action_cache_requests cas_find_missing_digests scheduler_executions
  scheduler_queue_duration runner_actions runner_stage_duration runner_blob_read_duration
  cascache_requests cascache_bytes
  bazel_invocations bazel_invocation_cache_hit_ratio rpc_server_call_duration)
deadline=$((SECONDS + 60))
while :; do
  curl -fsS "http://${PROM_ADDR}/metrics" >"${WORKDIR}/metrics.txt" 2>/dev/null || true
  missing=()
  for m in "${want[@]}"; do
    grep -q "^${m}" "${WORKDIR}/metrics.txt" || missing+=("${m}")
  done
  ((${#missing[@]} == 0)) && break
  ((SECONDS < deadline)) || fail "metrics missing: ${missing[*]}"
  sleep 5
done
echo "$(grep -vc '^#' "${WORKDIR}/metrics.txt") series"

echo "==> Checking cas's invocation summary log"
# The summary is logged in the same call that emits the root span, so it is
# already written. Read a bounded chunk and count matches. A pipeline that
# stops at the first match (grep -q) makes the producer exit on SIGPIPE, and
# pipefail then fails the check even though the line was there.
if command -v kubectl >/dev/null 2>&1; then
  logs="$(kubectl -n ci-substrate logs statefulset/cas --tail=4000 || true)"
  matches="$(grep -F "invocation finished" <<<"${logs}" | grep -F -c -- "${INVOCATION_ID}" || true)"
  [[ "${matches}" -ge 1 ]] || fail "cas logged no summary for ${INVOCATION_ID}"
fi

echo "telemetry e2e passed"

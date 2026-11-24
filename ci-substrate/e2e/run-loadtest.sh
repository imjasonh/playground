#!/usr/bin/env bash
# Load test for ci-substrate: runs stock Bazel builds against cas as two
# tenants under constant traffic, bursty traffic, and a mix of both, then
# checks that no errors arose. Not wired into CI (it needs a running cluster
# with port-forwards); run it manually after run-kind.sh.
#
#   bash e2e/run-loadtest.sh 127.0.0.1:18980
#
# Reports per-phase timing, throughput, error count, and checks runner pod
# restarts, cas logs, and cascache stats at the end.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAS_ADDR="${1:?usage: run-loadtest.sh <cas host:port>}"
BAZEL="${CI_SUBSTRATE_BAZEL:-/tmp/bazel}"
if [[ ! -x "${BAZEL}" ]]; then
  echo "Bazel not found at ${BAZEL}; set CI_SUBSTRATE_BAZEL" >&2
  exit 1
fi

INSTANCE_A="tenant-a"
INSTANCE_B="tenant-b"
TOKEN_A="tok-a"
TOKEN_B="tok-b"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/ci-substrate-loadtest-XXXXXX")"
ERRORS=0
TOTAL=0

cleanup() {
  for user in a b; do
    if [[ -d "${WORKDIR}/${user}/ws" ]]; then
      (cd "${WORKDIR}/${user}/ws" && "${BAZEL}" --output_user_root="${WORKDIR}/${user}/root" shutdown) >/dev/null 2>&1 || true
    fi
  done
  chmod -R u+w "${WORKDIR}" 2>/dev/null || true
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

SALT="$(date +%s)-${RANDOM}${RANDOM}"
for user in a b; do
  mkdir -p "${WORKDIR}/${user}/ws"
  cp -R "${ROOT}/e2e/loadtest/." "${WORKDIR}/${user}/ws/"
  echo "${SALT}" >"${WORKDIR}/${user}/ws/salt.txt"
  echo "input1-${SALT}" >"${WORKDIR}/${user}/ws/input1.txt"
  echo "input2-${SALT}" >"${WORKDIR}/${user}/ws/input2.txt"
done

# bz_build runs one Bazel build as a user in their tenant. It writes
# Bazel's output to the log and "ok" or "ERR: ..." to the log's .result
# file, so backgrounded callers can collect results after wait.
bz_build() {
  local user=$1 target=$2 log=$3 cmd=${4:-build}
  local instance=${INSTANCE_A} token=${TOKEN_A}
  if [[ "${user}" == b ]]; then instance=${INSTANCE_B}; token=${TOKEN_B}; fi
  local rc=0
  (
    cd "${WORKDIR}/${user}/ws"
    "${BAZEL}" --output_user_root="${WORKDIR}/${user}/root" "${cmd}" "${target}" \
      --remote_executor="grpc://${CAS_ADDR}" \
      --remote_instance_name="${instance}" \
      --remote_header=x-ci-substrate-tenant="${token}" \
      --remote_timeout=120 \
      --jobs=32 \
      --color=no --curses=no \
      --spawn_strategy=remote
  ) >"${log}" 2>&1 || rc=$?
  if [[ ${rc} -eq 0 ]]; then
    echo "ok" >"${log}.result"
  else
    local msg
    msg=$(grep -m1 -E "ERROR:|FAILED|timeout|PERMISSION_DENIED|Unavailable" "${log}" 2>/dev/null || echo "exit ${rc}")
    echo "ERR: ${msg}" >"${log}.result"
  fi
}

# collect_results reads every .result file matching a prefix and records
# pass/fail.
collect_results() {
  local prefix=$1
  for f in "${WORKDIR}/${prefix}"*.result; do
    [[ -f "${f}" ]] || continue
    TOTAL=$((TOTAL + 1))
    local r
    r=$(cat "${f}")
    if [[ "${r}" != ok ]]; then
      ERRORS=$((ERRORS + 1))
      echo "  ${r}" >&2
    fi
  done
}

cache_stats() {
  curl -s http://127.0.0.1:19090/stats 2>/dev/null || echo "{}"
}

check_pods() {
  local restarts
  restarts=$(kubectl --context kind-ci-substrate-e2e -n ci-substrate get pods -l app=runner \
    -o jsonpath='{range .items[*]}{.status.containerStatuses[0].restartCount}{" "}{end}' 2>/dev/null || echo "?")
  echo "runner restarts: ${restarts}"
  if echo "${restarts}" | grep -qv "^0 "; then
    return 1
  fi
  return 0
}

check_cas_logs() {
  local errs
  errs=$(kubectl --context kind-ci-substrate-e2e -n ci-substrate logs cas-0 --since=30m 2>/dev/null \
    | grep -icE "ERROR|panic|fatal" || true)
  echo "cas error lines: ${errs}"
  if [[ "${errs}" -gt 0 ]]; then
    return 1
  fi
  return 0
}

TARGETS=("//:small" "//:medium" "//:tree" "//:fanout_0" "//:fanout_3" "//:fanout_7")
FANOUT=8

echo "=== ci-substrate load test ==="
echo "Bazel: ${BAZEL}"
echo "CAS: ${CAS_ADDR}"
echo "Salt: ${SALT}"
echo "Initial cascache stats: $(cache_stats)"
echo ""

# ---- Phase 1: Constant traffic ----
echo "--- Phase 1: Constant traffic (40 sequential builds, interleaved A/B) ---"
P1_START=$(date +%s%N)
for i in $(seq 1 20); do
  target="${TARGETS[$((i % ${#TARGETS[@]}))]}"
  bz_build a "${target}" "${WORKDIR}/p1-a-${i}.log"
  bz_build b "${target}" "${WORKDIR}/p1-b-${i}.log"
done
collect_results "p1-"
P1_END=$(date +%s%N)
P1_MS=$(( (P1_END - P1_START) / 1000000 ))
echo "Phase 1: ${TOTAL} builds, ${ERRORS} errors, ${P1_MS} ms"
echo ""

# ---- Phase 2: Bursty traffic ----
echo "--- Phase 2: Bursty traffic (16 concurrent builds per burst, 3 bursts) ---"
P2_START=$(date +%s%N)
P2_BEFORE=${TOTAL}
P2_ERR_BEFORE=${ERRORS}
for burst in 1 2 3; do
  echo "  burst ${burst}: launching 16 concurrent builds..."
  for j in $(seq 0 $((FANOUT - 1))); do
    bz_build a "//:fanout_${j}" "${WORKDIR}/p2-${burst}-a-${j}.log" &
    bz_build b "//:fanout_${j}" "${WORKDIR}/p2-${burst}-b-${j}.log" &
  done
  wait
done
collect_results "p2-"
P2_END=$(date +%s%N)
P2_MS=$(( (P2_END - P2_START) / 1000000 ))
P2_BUILDS=$((TOTAL - P2_BEFORE))
P2_ERRORS=$((ERRORS - P2_ERR_BEFORE))
echo "Phase 2: ${P2_BUILDS} builds, ${P2_ERRORS} errors, ${P2_MS} ms"
echo ""

# ---- Phase 3: Mixed constant + bursty ----
echo "--- Phase 3: Mixed (constant background + 2 bursts) ---"
P3_START=$(date +%s%N)
P3_BEFORE=${TOTAL}
P3_ERR_BEFORE=${ERRORS}

# Burst 1: 8 concurrent from B while A does sequential background builds
for j in $(seq 0 $((FANOUT - 1))); do
  bz_build b "//:fanout_${j}" "${WORKDIR}/p3-burst1-b-${j}.log" &
done
for i in $(seq 1 10); do
  target="${TARGETS[$((i % ${#TARGETS[@]}))]}"
  bz_build a "${target}" "${WORKDIR}/p3-bg-a-${i}.log"
done
wait

# Burst 2: 12 concurrent from both
for j in $(seq 0 5); do
  bz_build a "//:fanout_${j}" "${WORKDIR}/p3-burst2-a-${j}.log" &
  bz_build b "//:fanout_${j}" "${WORKDIR}/p3-burst2-b-${j}.log" &
done
wait

collect_results "p3-"
P3_END=$(date +%s%N)
P3_MS=$(( (P3_END - P3_START) / 1000000 ))
P3_BUILDS=$((TOTAL - P3_BEFORE))
P3_ERRORS=$((ERRORS - P3_ERR_BEFORE))
echo "Phase 3: ${P3_BUILDS} builds, ${P3_ERRORS} errors, ${P3_MS} ms"
echo ""

# ---- Phase 4: Test execution under load ----
echo "--- Phase 4: Test execution under load (4 concurrent sh_tests) ---"
P4_START=$(date +%s%N)
P4_BEFORE=${TOTAL}
P4_ERR_BEFORE=${ERRORS}
for user in a b; do
  for i in 1 2; do
    bz_build "${user}" "//:smoke_test" "${WORKDIR}/p4-${user}-${i}.log" test
  done
done
wait
collect_results "p4-"
P4_END=$(date +%s%N)
P4_MS=$(( (P4_END - P4_START) / 1000000 ))
P4_BUILDS=$((TOTAL - P4_BEFORE))
P4_ERRORS=$((ERRORS - P4_ERR_BEFORE))
echo "Phase 4: ${P4_BUILDS} builds, ${P4_ERRORS} errors, ${P4_MS} ms"
echo ""

# ---- Summary ----
echo "=== Summary ==="
echo "Total builds: ${TOTAL}"
echo "Total errors: ${ERRORS}"
echo "Final cascache stats: $(cache_stats)"
echo ""

echo "--- Health checks ---"
if check_pods; then
  echo "OK: no runner pod restarts"
else
  echo "WARN: runner pods restarted during the test"
fi
if check_cas_logs; then
  echo "OK: no cas errors in logs"
else
  echo "WARN: cas logged errors during the test"
fi

if [[ ${ERRORS} -eq 0 ]]; then
  echo ""
  echo "=== LOAD TEST PASSED: ${TOTAL} builds, 0 errors ==="
else
  echo ""
  echo "=== LOAD TEST FAILED: ${ERRORS}/${TOTAL} builds failed ==="
  exit 1
fi

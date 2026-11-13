#!/usr/bin/env bash
# Build e2e/bazel with stock Bazel as two users in two tenants against one
# cas, and fail if either tenant can see or change the other's results.
# run-kind.sh runs it after cictl, so it gates CI; it also runs against any
# cluster that serves cas and has runners for both tenants.
#
#   bash e2e/run-bazel.sh 127.0.0.1:18980
#
# Each user has their own copy of the workspace and their own Bazel output
# root, as two developers on two machines would. Both copies hold the same
# salt, so the two users send byte-identical actions, and the checks are:
#
#   1. Tenant A builds and runs a test remotely. Tenant B then builds the same
#      action: it is not an action cache hit, and it runs on B's runner.
#   2. Both tenants build the same fan-out of actions at the same time. Every
#      output is from the builder's own runner: the scheduler never merges two
#      tenants' identical actions into one run.
#   3. After a clean build, each tenant's rebuild is an action cache hit with
#      its own runner's output, so B's run did not replace A's entry.
#   4. Tenant A runs an action locally and uploads the result to its action
#      cache. A's remote build of it is a cache hit with A's local output, and
#      B's build of the same action runs on B's runner.
#   5. Tenant A's token cannot build in tenant B's instance.
#
# Outputs end with the hostname of the machine that ran the action. The
# runner hostnames start with CI_SUBSTRATE_BAZEL_RUNNER_A and
# CI_SUBSTRATE_BAZEL_RUNNER_B (runner-tenant-a- and runner-tenant-b-, the
# Deployments in deploy/40-runner.yaml).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAS_ADDR="${1:?usage: run-bazel.sh <cas host:port>}"
BAZEL_VERSION="$(cat "${ROOT}/e2e/bazel/.bazelversion")"
RUNNER_A="${CI_SUBSTRATE_BAZEL_RUNNER_A:-runner-tenant-a-}"
RUNNER_B="${CI_SUBSTRATE_BAZEL_RUNNER_B:-runner-tenant-b-}"
INSTANCE_A="${CI_SUBSTRATE_BAZEL_INSTANCE_A:-tenant-a}"
INSTANCE_B="${CI_SUBSTRATE_BAZEL_INSTANCE_B:-tenant-b}"
TOKEN_A="${CI_SUBSTRATE_BAZEL_TOKEN_A:-tok-a}"
TOKEN_B="${CI_SUBSTRATE_BAZEL_TOKEN_B:-tok-b}"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/ci-substrate-bazel-XXXXXX")"
BAZEL_PIDS=()

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# shellcheck source=lib-bazel.sh
source "${ROOT}/e2e/lib-bazel.sh"

BAZEL="${CI_SUBSTRATE_BAZEL:-$(install_bazel "${BAZEL_VERSION}")}"

cleanup() {
  local user pid
  for pid in "${BAZEL_PIDS[@]:-}"; do
    [[ -n "${pid}" ]] && kill "${pid}" 2>/dev/null || true
  done
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
  cp -R "${ROOT}/e2e/bazel/." "${WORKDIR}/${user}/ws/"
  echo "${SALT}" >"${WORKDIR}/${user}/ws/salt.txt"
done

# bz runs Bazel as one user: bz <a|b> <instance> <token> <log> <command> [args...].
# Its output goes to the log; the exit code is Bazel's.
bz() {
  local user=$1 instance=$2 token=$3 log=$4 cmd=$5
  shift 5
  (
    cd "${WORKDIR}/${user}/ws"
    "${BAZEL}" --output_user_root="${WORKDIR}/${user}/root" "${cmd}" \
      --remote_instance_name="${instance}" \
      --remote_header=x-ci-substrate-tenant="${token}" \
      --remote_timeout=120 \
      --jobs=32 \
      --color=no --curses=no \
      "$@"
  ) >"${log}" 2>&1
}

# remote runs an action remotely in the user's own tenant.
remote() {
  local user=$1 log=$2 cmd=$3
  shift 3
  local instance=${INSTANCE_A} token=${TOKEN_A}
  if [[ "${user}" == b ]]; then
    instance=${INSTANCE_B} token=${TOKEN_B}
  fi
  bz "${user}" "${instance}" "${token}" "${log}" "${cmd}" \
    --remote_executor="grpc://${CAS_ADDR}" --spawn_strategy=remote "$@" ||
    { cat "${log}" >&2; fail "user ${user}: bazel ${cmd} $*"; }
}

# processes prints Bazel's process summary from a log, e.g.
# "4 processes: 1 internal, 3 remote."
processes() {
  grep -E '^INFO: [0-9]+ process(es)?: ' "$1" | tail -1
}

# expect_executed fails unless the log shows n remote executions and no
# action cache hits.
expect_executed() {
  local log=$1 n=$2 summary
  summary="$(processes "${log}")"
  [[ "${summary}" != *"remote cache hit"* ]] || fail "expected no action cache hits: ${summary}"
  [[ "${summary}" == *" ${n} remote."* ]] || fail "expected ${n} remote executions: ${summary}"
}

# expect_cache_hits fails unless the log shows n action cache hits and no
# executions.
expect_cache_hits() {
  local log=$1 n=$2 summary
  summary="$(processes "${log}")"
  [[ "${summary}" == *"${n} remote cache hit"* ]] || fail "expected ${n} action cache hits: ${summary}"
  [[ ! "${summary}" =~ [0-9]+\ remote\. ]] || fail "expected no remote executions: ${summary}"
}

# expect_ran_on fails unless the output file's salt is this run's and its
# last line, the hostname that ran it, starts with prefix.
expect_ran_on() {
  local file=$1 prefix=$2 host
  [[ "$(head -1 "${file}")" == "${SALT}" ]] || fail "${file} is from another run: $(head -1 "${file}")"
  host="$(tail -1 "${file}")"
  [[ "${host}" == "${prefix}"* ]] || fail "${file} ran on ${host}, want ${prefix}*"
}

bin() {
  echo "${WORKDIR}/$1/ws/bazel-bin/$2"
}

echo "==> Bazel ${BAZEL_VERSION} against ${CAS_ADDR}: ${INSTANCE_A} and ${INSTANCE_B}"

echo "--> 1. A builds and tests; B's identical action runs on B's runner"
remote a "${WORKDIR}/1a.log" build //:whoami
expect_executed "${WORKDIR}/1a.log" 1
expect_ran_on "$(bin a whoami.txt)" "${RUNNER_A}"
# The test's XML report reads only the test log, which is the same in every
# run, so the test is checked for passing, not for its process counts.
remote a "${WORKDIR}/1a-test.log" test //:whoami_test
grep -q '//:whoami_test .*PASSED' "${WORKDIR}/1a-test.log" || { cat "${WORKDIR}/1a-test.log" >&2; fail "//:whoami_test did not pass remotely"; }
remote b "${WORKDIR}/1b.log" build //:whoami
expect_executed "${WORKDIR}/1b.log" 1
expect_ran_on "$(bin b whoami.txt)" "${RUNNER_B}"

echo "--> 2. A and B build the same fan-out at once"
fanout="$(grep -oE '^FANOUT = [0-9]+' "${ROOT}/e2e/bazel/BUILD.bazel" | grep -oE '[0-9]+')"
remote a "${WORKDIR}/2a.log" build //:fanout &
BAZEL_PIDS+=($!)
remote b "${WORKDIR}/2b.log" build //:fanout &
BAZEL_PIDS+=($!)
for pid in "${BAZEL_PIDS[@]}"; do
  wait "${pid}" || fail "a concurrent build failed"
done
BAZEL_PIDS=()
expect_executed "${WORKDIR}/2a.log" "${fanout}"
expect_executed "${WORKDIR}/2b.log" "${fanout}"
for ((i = 0; i < fanout; i++)); do
  expect_ran_on "$(bin a "fanout_${i}.txt")" "${RUNNER_A}"
  expect_ran_on "$(bin b "fanout_${i}.txt")" "${RUNNER_B}"
done

echo "--> 3. After a clean, each tenant's rebuild is its own cache hit"
for user in a b; do
  (cd "${WORKDIR}/${user}/ws" && "${BAZEL}" --output_user_root="${WORKDIR}/${user}/root" clean) >/dev/null 2>&1
done
remote a "${WORKDIR}/3a.log" build //:whoami //:fanout
expect_cache_hits "${WORKDIR}/3a.log" "$((fanout + 1))"
expect_ran_on "$(bin a whoami.txt)" "${RUNNER_A}"
expect_ran_on "$(bin a fanout_0.txt)" "${RUNNER_A}"
remote b "${WORKDIR}/3b.log" build //:whoami //:fanout
expect_cache_hits "${WORKDIR}/3b.log" "$((fanout + 1))"
expect_ran_on "$(bin b whoami.txt)" "${RUNNER_B}"
expect_ran_on "$(bin b fanout_0.txt)" "${RUNNER_B}"

echo "--> 4. A uploads a local result; B does not get it"
local_host="$(hostname)"
bz a "${INSTANCE_A}" "${TOKEN_A}" "${WORKDIR}/4a-local.log" build //:uploaded \
  --remote_cache="grpc://${CAS_ADDR}" --spawn_strategy=local --remote_upload_local_results ||
  { cat "${WORKDIR}/4a-local.log" >&2; fail "user a: local build with upload"; }
expect_ran_on "$(bin a uploaded.txt)" "${local_host}"
(cd "${WORKDIR}/a/ws" && "${BAZEL}" --output_user_root="${WORKDIR}/a/root" clean) >/dev/null 2>&1
# The upload has to reach A's action cache for B's check to mean anything.
remote a "${WORKDIR}/4a.log" build //:uploaded
expect_cache_hits "${WORKDIR}/4a.log" 1
expect_ran_on "$(bin a uploaded.txt)" "${local_host}"
remote b "${WORKDIR}/4b.log" build //:uploaded
expect_executed "${WORKDIR}/4b.log" 1
expect_ran_on "$(bin b uploaded.txt)" "${RUNNER_B}"

echo "--> 5. A's token cannot build in B's instance"
if bz a "${INSTANCE_B}" "${TOKEN_A}" "${WORKDIR}/5.log" build //:whoami \
  --remote_executor="grpc://${CAS_ADDR}" --spawn_strategy=remote; then
  fail "tenant A's token built in ${INSTANCE_B}"
fi
grep -q PERMISSION_DENIED "${WORKDIR}/5.log" || { cat "${WORKDIR}/5.log" >&2; fail "build in ${INSTANCE_B} failed, but not with PERMISSION_DENIED"; }

echo "==> Bazel tenant isolation held"

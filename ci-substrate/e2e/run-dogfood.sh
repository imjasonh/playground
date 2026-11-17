#!/usr/bin/env bash
# Build and test ci-substrate with Bazel on ci-substrate: every action of the
# repository's own build runs on the cluster's runners. run-kind.sh runs it
# after run-bazel.sh; it also runs against any cluster that serves cas and
# has runners for the tenant.
#
#   bash e2e/run-dogfood.sh 127.0.0.1:18980
#
# The checks are:
#
#   1. The BUILD files are what Gazelle writes. Gazelle itself is built on
#      the cluster.
#   2. bazel build //... executes every action remotely, without taking
#      results an earlier run left in the cluster: none runs on the host.
#   3. bazel test //... passes, with each test run on a runner.
#   4. After a clean, the rebuild is all action cache hits: the cluster
#      serves a real build's results back.
#
# The host fetches the Go SDK and Go modules, so it needs to reach
# dl.google.com and proxy.golang.org. The runners need nothing but cas.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAS_ADDR="${1:?usage: run-dogfood.sh <cas host:port>}"
INSTANCE="${CI_SUBSTRATE_DOGFOOD_INSTANCE:-tenant-a}"
TOKEN="${CI_SUBSTRATE_DOGFOOD_TOKEN:-tok-a}"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/ci-substrate-dogfood-XXXXXX")"
WS="${WORKDIR}/ws"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# shellcheck source=lib-bazel.sh
source "${ROOT}/e2e/lib-bazel.sh"

BAZEL="${CI_SUBSTRATE_BAZEL:-$(install_bazel "$(cat "${ROOT}/.bazelversion")")}"

cleanup() {
  if [[ -d "${WS}" ]]; then
    (cd "${WS}" && "${BAZEL}" --output_user_root="${WORKDIR}/root" shutdown) >/dev/null 2>&1 || true
  fi
  chmod -R u+w "${WORKDIR}" 2>/dev/null || true
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

# The workspace is a copy of the checkout's files, without its bazel-*
# symlinks or any local Bazel state.
mkdir -p "${WS}"
git -C "${ROOT}" ls-files -z --cached --others --exclude-standard . |
  (cd "${ROOT}" && tar --null -T - -cf -) | tar -C "${WS}" -xf -

# bz runs Bazel against the cluster: bz <log> <command> [args...]. Its output
# goes to the log; the exit code is Bazel's.
bz() {
  local log=$1 cmd=$2
  shift 2
  (
    cd "${WS}"
    "${BAZEL}" --output_user_root="${WORKDIR}/root" "${cmd}" \
      --remote_executor="grpc://${CAS_ADDR}" \
      --remote_instance_name="${INSTANCE}" \
      --remote_header=x-ci-substrate-tenant="${TOKEN}" \
      --spawn_strategy=remote \
      --remote_timeout=300 \
      --jobs=32 \
      --color=no --curses=no \
      "$@"
  ) >"${log}" 2>&1
}

# processes prints Bazel's process summary from a log, e.g.
# "382 processes: 36 action cache hit, 69 internal, 313 remote."
processes() {
  grep -E '^INFO: [0-9]+ process(es)?: ' "$1" | tail -1
}

# expect_all_remote fails unless every process in the log's summary was a
# remote execution, an action cache hit, or internal to Bazel.
expect_all_remote() {
  local log=$1 summary rest
  summary="$(processes "${log}")"
  [[ -n "${summary}" ]] || fail "no process summary in ${log}"
  rest="$(sed -E 's/^INFO: [0-9]+ process(es)?: //; s/\.$//' <<<"${summary}" | tr ',' '\n' |
    sed -E 's/^ *//' | grep -vE '^[0-9]+ (internal|remote|remote cache hit|action cache hit)$' || true)"
  [[ -z "${rest}" ]] || fail "processes ran outside the cluster (${rest//$'\n'/, }): ${summary}"
}

elapsed() {
  grep -oE '^INFO: Elapsed time: [0-9.]+s' "$1" | grep -oE '[0-9.]+s'
}

echo "==> ci-substrate on ci-substrate: Bazel against ${CAS_ADDR} as ${INSTANCE}"

echo "--> 1. The BUILD files are up to date"
log="${WORKDIR}/gazelle.log"
bz "${log}" run //:gazelle -- -mode=diff || { cat "${log}" >&2; fail "BUILD files are stale; run bazel run //:gazelle"; }
expect_all_remote "${log}"

echo "--> 2. bazel build //... runs every action on the cluster"
log="${WORKDIR}/build.log"
# Results from an earlier run on this cluster are not looked up, so every
# action executes on a runner however warm the cluster is.
bz "${log}" build //... --noremote_accept_cached || { cat "${log}" >&2; fail "bazel build //..."; }
expect_all_remote "${log}"
grep -qE ' [0-9]+ remote[.,]' <<<"$(processes "${log}")" || fail "nothing ran remotely: $(processes "${log}")"
echo "    $(processes "${log}" | sed 's/^INFO: //') in $(elapsed "${log}")"

echo "--> 3. bazel test //... passes on the cluster"
log="${WORKDIR}/test.log"
bz "${log}" test //... --noremote_accept_cached || { cat "${log}" >&2; fail "bazel test //..."; }
expect_all_remote "${log}"
summary="$(grep -E '^Executed [0-9]+ out of [0-9]+ tests' "${log}")"
echo "    ${summary}"
[[ "${summary}" != "Executed 0 out of"* ]] || fail "no test ran: ${summary}"

echo "--> 4. After a clean, the rebuild is all action cache hits"
(cd "${WS}" && "${BAZEL}" --output_user_root="${WORKDIR}/root" clean) >/dev/null 2>&1
log="${WORKDIR}/rebuild.log"
bz "${log}" build //... || { cat "${log}" >&2; fail "bazel build //... after clean"; }
expect_all_remote "${log}"
summary="$(processes "${log}")"
[[ ! "${summary}" =~ [0-9]+\ remote[.,] ]] || fail "rebuild executed actions: ${summary}"
[[ "${summary}" == *"remote cache hit"* ]] || fail "rebuild had no action cache hits: ${summary}"
echo "    $(sed 's/^INFO: //' <<<"${summary}") in $(elapsed "${log}")"

echo "PASS: ci-substrate built and tested itself on ci-substrate"

#!/usr/bin/env bash
# Stop what setup.sh started: the git server, the module proxy, the kind
# cluster, and the registry. The state directory stays, with its logs and
# runs; remove it yourself when you don't need them.
#
# Environment variables:
#   GK_STRESS_STATE  the directory that setup.sh used (default /tmp/gk-stress)
set -euo pipefail

STATE="${GK_STRESS_STATE:-/tmp/gk-stress}"
if [[ ! -f "${STATE}/env" ]]; then
  echo "no ${STATE}/env; set GK_STRESS_STATE to the directory that setup.sh used" >&2
  exit 1
fi
# shellcheck disable=SC1091
source "${STATE}/env"

# stop kills the process with PID $1 if it runs the command $2, so a PID
# that another process took after a reboot is left alone.
stop() {
  if [[ -n "$1" && "$(ps -p "$1" -o comm= 2>/dev/null)" == "$2" ]]; then
    kill "$1"
  fi
}
stop "${GIT_SERVER_PID:-}" gitserver
stop "${MOD_PROXY_PID:-}" modproxy
if kind get clusters 2>/dev/null | grep -qx "${CLUSTER}"; then
  kind delete cluster --name "${CLUSTER}"
fi
if docker inspect "${REGISTRY}" >/dev/null 2>&1; then
  docker rm -f "${REGISTRY}" >/dev/null
fi
echo "Stopped ${CLUSTER} and ${REGISTRY}; ${STATE} still has the logs and runs"

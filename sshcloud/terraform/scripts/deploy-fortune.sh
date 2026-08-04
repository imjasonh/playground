#!/usr/bin/env bash
# Hacky bootstrap: join as "demo" then non-interactively deploy fortune.
#
#   DEMO_KEY_PEM=... HOST_PUB=... \
#     bash deploy-fortune.sh GATEWAY_IP IMAGE_REF
set -euo pipefail

IP="${1:?gateway IP}"
IMAGE="${2:?digest-pinned fortune image}"
USER_NAME="${DEPLOY_USER:-demo}"
APP_NAME="${DEPLOY_APP:-fortune}"
TIER="${DEPLOY_TIER:-tiny}"
STRATEGY="${DEPLOY_STRATEGY:-kick}"
RETRIES="${DEPLOY_RETRIES:-36}"
SLEEP_SECS="${DEPLOY_SLEEP:-10}"
REQUEST_TIMEOUT="${DEPLOY_REQUEST_TIMEOUT:-360}"
TOTAL_TIMEOUT="${DEPLOY_TOTAL_TIMEOUT:-1200}"

if [[ -z "${DEMO_KEY_PEM:-}" || -z "${HOST_PUB:-}" ]]; then
  echo "DEMO_KEY_PEM and HOST_PUB env vars are required" >&2
  exit 1
fi
if [[ ! "$USER_NAME" =~ ^[a-z][a-z0-9-]{2,31}$ ]] || [[ ! "$APP_NAME" =~ ^[a-z][a-z0-9-]{2,31}$ ]]; then
  echo "DEPLOY_USER and DEPLOY_APP must match [a-z][a-z0-9-]{2,31}" >&2
  exit 2
fi
if [[ "$TIER" != "tiny" && "$TIER" != "small" ]]; then
  echo "DEPLOY_TIER must be tiny or small" >&2
  exit 2
fi
if [[ "$STRATEGY" != "kick" && "$STRATEGY" != "drain" ]]; then
  echo "DEPLOY_STRATEGY must be kick or drain" >&2
  exit 2
fi
for value in "$RETRIES" "$SLEEP_SECS" "$REQUEST_TIMEOUT" "$TOTAL_TIMEOUT"; do
  if [[ ! "$value" =~ ^[0-9]+$ ]] || [[ "$value" -eq 0 ]]; then
    echo "retry and timeout settings must be positive integers" >&2
    exit 2
  fi
done
deadline=$((SECONDS + TOTAL_TIMEOUT))

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
key="$tmpdir/demo"
known="$tmpdir/known_hosts"
printf '%s\n' "$DEMO_KEY_PEM" >"$key"
chmod 600 "$key"
pub_type="$(echo "$HOST_PUB" | awk '{print $1}')"
pub_b64="$(echo "$HOST_PUB" | awk '{print $2}')"
echo "${IP} ${pub_type} ${pub_b64}" >"$known"

ssh_base=(
  ssh
  -p 22
  -i "$key"
  -o IdentitiesOnly=yes
  -o UserKnownHostsFile="$known"
  -o GlobalKnownHostsFile=/dev/null
  -o StrictHostKeyChecking=yes
  -o ConnectTimeout=10
  -o BatchMode=yes
)

run_ssh() {
  timeout --signal=TERM --kill-after=5 "$REQUEST_TIMEOUT" "${ssh_base[@]}" "$@"
}

pause_retry() {
  if (( SECONDS + SLEEP_SECS >= deadline )); then
    return 1
  fi
  sleep "$SLEEP_SECS"
}

port_open() {
  if command -v nc >/dev/null 2>&1; then
    nc -z -w 2 "$IP" 22
  else
    timeout 2 bash -c "echo >/dev/tcp/${IP}/22"
  fi
}

echo "waiting for gateway SSH on ${IP}:22 …"
ok=0
for i in $(seq 1 "$RETRIES"); do
  if (( SECONDS >= deadline )); then
    break
  fi
  if port_open 2>/dev/null; then
    ok=1
    break
  fi
  echo "  attempt ${i}/${RETRIES}: port closed, sleep ${SLEEP_SECS}s"
  pause_retry || break
done
if [[ "$ok" -ne 1 ]]; then
  echo "gateway SSH never became ready" >&2
  exit 1
fi

echo "joining as ${USER_NAME}…"
joined=0
for i in $(seq 1 "$RETRIES"); do
  if (( SECONDS >= deadline )); then
    break
  fi
  set +e
  join_out="$(run_ssh "join@${IP}" "${USER_NAME}" 2>&1)"
  join_rc=$?
  set -e
  echo "$join_out"
  if [[ "$join_rc" -eq 0 ]]; then
    joined=1
    break
  fi
  echo "  join attempt ${i}/${RETRIES} failed (rc=${join_rc}); sleep ${SLEEP_SECS}s"
  pause_retry || break
done
if [[ "$joined" -ne 1 ]]; then
  echo "join failed" >&2
  exit 1
fi

echo "deploying ${APP_NAME} ← ${IMAGE}"
deploy_args=(
  "$APP_NAME"
  "--image=$IMAGE"
  "--tier=$TIER"
  "--strategy=$STRATEGY"
  "--yes"
)
for i in $(seq 1 "$RETRIES"); do
  if (( SECONDS >= deadline )); then
    break
  fi
  set +e
  last="$(run_ssh "deploy@${IP}" "${deploy_args[@]}" 2>&1)"
  rc=$?
  set -e
  echo "$last"
  if [[ "$rc" -eq 0 ]]; then
    echo "fortune deploy ok"
    exit 0
  fi
  echo "  deploy attempt ${i}/${RETRIES} failed (rc=${rc}); sleep ${SLEEP_SECS}s"
  pause_retry || break
done
echo "deploy failed before the ${TOTAL_TIMEOUT}s overall deadline" >&2
exit 1

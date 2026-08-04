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

if [[ -z "${DEMO_KEY_PEM:-}" || -z "${HOST_PUB:-}" ]]; then
  echo "DEMO_KEY_PEM and HOST_PUB env vars are required" >&2
  exit 1
fi

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
  if port_open 2>/dev/null; then
    ok=1
    break
  fi
  echo "  attempt ${i}/${RETRIES}: port closed, sleep ${SLEEP_SECS}s"
  sleep "$SLEEP_SECS"
done
if [[ "$ok" -ne 1 ]]; then
  echo "gateway SSH never became ready" >&2
  exit 1
fi

echo "joining as ${USER_NAME}…"
# First apply: creates user. Later applies: key already known → "Logged in as …".
set +e
join_out="$("${ssh_base[@]}" "join@${IP}" "${USER_NAME}" 2>&1)"
join_rc=$?
set -e
echo "$join_out"
if [[ "$join_rc" -ne 0 ]] && ! echo "$join_out" | grep -qE "Joined as ${USER_NAME}|Logged in as ${USER_NAME}"; then
  # Gateway may still be starting (handshake fails). Retry join a few times.
  joined=0
  for i in $(seq 1 "$RETRIES"); do
    set +e
    join_out="$("${ssh_base[@]}" "join@${IP}" "${USER_NAME}" 2>&1)"
    join_rc=$?
    set -e
    echo "$join_out"
    if [[ "$join_rc" -eq 0 ]] || echo "$join_out" | grep -qE "Joined as ${USER_NAME}|Logged in as ${USER_NAME}"; then
      joined=1
      break
    fi
    echo "  join attempt ${i}/${RETRIES} failed; sleep ${SLEEP_SECS}s"
    sleep "$SLEEP_SECS"
  done
  if [[ "$joined" -ne 1 ]]; then
    echo "join failed" >&2
    exit 1
  fi
fi

echo "deploying ${APP_NAME} ← ${IMAGE}"
deploy_cmd="${APP_NAME} --image=${IMAGE} --tier=${TIER} --strategy=${STRATEGY} --yes"
for i in $(seq 1 "$RETRIES"); do
  set +e
  last="$("${ssh_base[@]}" "deploy@${IP}" ${deploy_cmd} 2>&1)"
  rc=$?
  set -e
  echo "$last"
  if [[ "$rc" -eq 0 ]]; then
    echo "fortune deploy ok"
    exit 0
  fi
  echo "  deploy attempt ${i}/${RETRIES} failed (rc=${rc}); sleep ${SLEEP_SECS}s"
  sleep "$SLEEP_SECS"
done
echo "deploy failed after ${RETRIES} attempts (agents/assets may still be warming)" >&2
exit 1

#!/usr/bin/env bash
# Verify the released fortune app through the public gateway with pinned keys.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=ssh-client.sh
source "$SCRIPT_DIR/ssh-client.sh"

IP="${1:?gateway IP}"
APP_NAME="${2:?app name}"
USER_NAME="${VERIFY_USER:-demo}"
RETRIES="${VERIFY_RETRIES:-12}"
SLEEP_SECS="${VERIFY_SLEEP:-5}"
REQUEST_TIMEOUT="${VERIFY_REQUEST_TIMEOUT:-360}"
TOTAL_TIMEOUT="${VERIFY_TOTAL_TIMEOUT:-900}"
EXPECTED="${VERIFY_EXPECTED:-hello $USER_NAME}"

if [[ ! "$APP_NAME" =~ ^[a-z][a-z0-9-]{2,31}$ ]] ||
  [[ ! "$USER_NAME" =~ ^[a-z][a-z0-9-]{2,31}$ ]]; then
  echo "VERIFY_USER and app name must match [a-z][a-z0-9-]{2,31}" >&2
  exit 2
fi
for value in "$RETRIES" "$SLEEP_SECS" "$REQUEST_TIMEOUT" "$TOTAL_TIMEOUT"; do
  if [[ ! "$value" =~ ^[0-9]+$ ]] || [[ "$value" -eq 0 ]]; then
    echo "retry and timeout settings must be positive integers" >&2
    exit 2
  fi
done

deadline=$((SECONDS + TOTAL_TIMEOUT))
ssh_client_init "$IP" "$REQUEST_TIMEOUT"

for ((i = 1; i <= RETRIES && SECONDS < deadline; i += 1)); do
  set +e
  output="$(ssh_run -T "${APP_NAME}@${IP}" </dev/null 2>&1)"
  rc=$?
  set -e
  printf '%s\n' "$output"
  if [[ "$rc" -eq 0 && "$output" == *"$EXPECTED"* ]]; then
    echo "fortune SSH smoke test ok"
    exit 0
  fi
  if [[ "$rc" -eq 0 ]]; then
    echo "attempt ${i}/${RETRIES}: output did not contain: $EXPECTED" >&2
  else
    echo "attempt ${i}/${RETRIES}: SSH exited ${rc}" >&2
  fi
  if ((i < RETRIES && SECONDS + SLEEP_SECS < deadline)); then
    sleep "$SLEEP_SECS"
  fi
done

echo "fortune SSH smoke test failed before the ${TOTAL_TIMEOUT}s overall deadline" >&2
exit 1

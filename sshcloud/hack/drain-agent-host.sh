#!/usr/bin/env bash
# Cordon and drain one agent before a managed-instance replacement.
set -euo pipefail

ORCHESTRATOR_URL="${1:?usage: drain-agent-host.sh ORCHESTRATOR_URL HOST_ID TOKEN_FILE}"
HOST_ID="${2:?host ID}"
TOKEN_FILE="${3:?orchestrator control-token file}"
TOKEN="$(tr -d '\r\n' <"$TOKEN_FILE")"
if [[ -z "$TOKEN" ]]; then
  echo "empty token in $TOKEN_FILE" >&2
  exit 1
fi
BODY="$(HOST_ID="$HOST_ID" python3 - <<'PY'
import json, os
print(json.dumps({"host": os.environ["HOST_ID"]}))
PY
)"

curl --fail-with-body --silent --show-error \
  --connect-timeout 10 --max-time 1800 \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  --data "$BODY" \
  "${ORCHESTRATOR_URL%/}/v1/hosts/drain"
echo
echo "host $HOST_ID is cordoned and empty; it is safe to replace"

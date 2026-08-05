#!/usr/bin/env bash
# Run on the orchestrator VM (reached with IAP + OS Login) to cordon and drain
# one agent before a managed-instance replacement. The admin API never listens
# on TCP; root access to its Unix socket and role files is still followed by
# mTLS plus a fresh audience-bound GCE identity token.
set -euo pipefail

HOST_ID="${1:?usage: drain-agent-host.sh HOST_ID [ADMIN_SOCKET] [CONTROL_DIR]}"
ADMIN_SOCKET="${2:-/run/sshcloud/orchestrator-admin.sock}"
CONTROL_DIR="${3:-/var/lib/sshcloud/control}"
if [[ "$EUID" -ne 0 ]]; then
  echo "run as root on the orchestrator VM (for example through sudo after IAP/OS Login)" >&2
  exit 1
fi
AUDIENCE="https://control.sshcloud.internal/orchestrator/admin"
TOKEN="$(curl --fail --silent --show-error \
  -H 'Metadata-Flavor: Google' \
  --get --data-urlencode "audience=$AUDIENCE" --data-urlencode 'format=full' \
  http://metadata.google.internal/computeMetadata/v1/instance/service-accounts/default/identity)"
BODY="$(HOST_ID="$HOST_ID" python3 - <<'PY'
import json, os
print(json.dumps({"host": os.environ["HOST_ID"]}))
PY
)"
CA_BUNDLE="$(mktemp)"
trap 'rm -f "$CA_BUNDLE"' EXIT
cat "$CONTROL_DIR/ca-current.pem" "$CONTROL_DIR/ca-previous.pem" >"$CA_BUNDLE"
chmod 0600 "$CA_BUNDLE"

curl --fail-with-body --silent --show-error \
  --connect-timeout 10 --max-time 1800 \
  --unix-socket "$ADMIN_SOCKET" \
  --cacert "$CA_BUNDLE" \
  --cert "$CONTROL_DIR/tls.crt" \
  --key "$CONTROL_DIR/tls.key" \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  --data "$BODY" \
  "https://orchestrator.control.sshcloud.internal/v1/hosts/drain"
echo
echo "host $HOST_ID is cordoned and empty; it is safe to replace"

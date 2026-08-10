#!/usr/bin/env bash
# Ensure a Worker that ships examples/gensecret.rs has an UPLOAD_SECRET secret.
#
# Run AFTER `wrangler deploy` (wrangler-action postCommands), from the Worker
# app directory. The secret is generated only when absent, so redeploys keep
# the same shared token the ESP32 / curl uploaders already know.
#
# Environment:
#   CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID  (wrangler-action provides both)
set -euo pipefail

if [ ! -f examples/gensecret.rs ]; then
  echo "No examples/gensecret.rs here; skipping UPLOAD_SECRET management."
  exit 0
fi

: "${CLOUDFLARE_API_TOKEN:?CLOUDFLARE_API_TOKEN must be set}"
: "${CLOUDFLARE_ACCOUNT_ID:?CLOUDFLARE_ACCOUNT_ID must be set}"

script_name=$(python3 - <<'PY'
import tomllib
with open("wrangler.toml", "rb") as fh:
    print(tomllib.load(fh).get("name", ""))
PY
)
if [ -z "$script_name" ]; then
  echo "wrangler.toml has no top-level name; cannot manage secrets." >&2
  exit 1
fi

api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}"

resp=$(curl --fail-with-body -sS \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  "${api}/workers/scripts/${script_name}/secrets")

if [ "$(printf '%s' "$resp" | jq -r '.success')" != "true" ]; then
  echo "Failed to list secrets for ${script_name}: ${resp}" >&2
  exit 1
fi

if printf '%s' "$resp" | jq -e '.result[]? | select(.name=="UPLOAD_SECRET")' >/dev/null; then
  echo "UPLOAD_SECRET already set on ${script_name}; leaving it unchanged."
  exit 0
fi

echo "UPLOAD_SECRET not set on ${script_name}; generating a new secret."
secret=$(cargo run --quiet --example gensecret | sed -n 's/^UPLOAD_SECRET=//p')
if [ -z "$secret" ]; then
  echo "Failed to generate an upload secret via gensecret example." >&2
  exit 1
fi

body=$(jq -nc --arg text "$secret" '{name: "UPLOAD_SECRET", text: $text, type: "secret_text"}')
resp=$(printf '%s' "$body" | curl --fail-with-body -sS -X PUT \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  -H "Content-Type: application/json" \
  --data @- \
  "${api}/workers/scripts/${script_name}/secrets")

if [ "$(printf '%s' "$resp" | jq -r '.success')" != "true" ]; then
  echo "Failed to set UPLOAD_SECRET on ${script_name}: ${resp}" >&2
  exit 1
fi
echo "UPLOAD_SECRET set on ${script_name}."

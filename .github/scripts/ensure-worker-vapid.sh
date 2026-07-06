#!/usr/bin/env bash
# Ensure a Worker that ships examples/genvapid.rs has a VAPID_PRIVATE_KEY secret.
#
# Run this AFTER `wrangler deploy` (wrangler-action postCommands), from the
# Worker app directory, so the Worker script exists and can hold a secret. The
# key is generated only when the secret is absent, so redeploys keep the same
# VAPID identity and existing browser subscriptions stay valid.
#
# Environment:
#   CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID  (wrangler-action provides both)
set -euo pipefail

# Only workers that ship a genvapid example manage a VAPID key this way.
if [ ! -f examples/genvapid.rs ]; then
  echo "No examples/genvapid.rs here; skipping VAPID secret management."
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

# List the deployed Worker's secrets. This runs post-deploy, so the script must
# exist; a failure here is fatal rather than silently regenerating (which would
# rotate the VAPID key and break existing subscriptions).
resp=$(curl --fail-with-body -sS \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  "${api}/workers/scripts/${script_name}/secrets")

if [ "$(printf '%s' "$resp" | jq -r '.success')" != "true" ]; then
  echo "Failed to list secrets for ${script_name}: ${resp}" >&2
  exit 1
fi

if printf '%s' "$resp" | jq -e '.result[]? | select(.name=="VAPID_PRIVATE_KEY")' >/dev/null; then
  echo "VAPID_PRIVATE_KEY already set on ${script_name}; leaving it unchanged."
  exit 0
fi

echo "VAPID_PRIVATE_KEY not set on ${script_name}; generating a new key pair."
private_key=$(cargo run --quiet --example genvapid | sed -n 's/^VAPID_PRIVATE_KEY=//p')
if [ -z "$private_key" ]; then
  echo "Failed to generate a VAPID private key via genvapid example." >&2
  exit 1
fi

printf '%s' "$private_key" | wrangler secret put VAPID_PRIVATE_KEY
echo "VAPID_PRIVATE_KEY set on ${script_name}."

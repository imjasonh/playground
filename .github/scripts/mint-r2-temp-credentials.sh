#!/usr/bin/env bash
# Mint short-lived R2 S3 credentials for Terraform state via the Cloudflare
# Temporary Credentials API, then export them for subsequent steps.
#
# Uses the existing CLOUDFLARE_API_TOKEN as Bearer auth and an R2 Access Key ID
# (TF_STATE_R2_ACCESS_KEY_ID) as the parent token to derive from. Does not need
# the parent secret key — Cloudflare signs the session server-side.
#
# Writes AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, and AWS_SESSION_TOKEN to
# GITHUB_ENV when set (and exports them in this shell).
#
# Environment:
#   CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID
#   TF_STATE_R2_ACCESS_KEY_ID  Parent R2 Access Key ID (dashboard "Manage R2 API tokens")
#   TF_STATE_R2_BUCKET         (default: playground-terraform-state)
#   TF_STATE_R2_PREFIX         Optional prefix scope (default: exe/)
#   TF_STATE_R2_TTL_SECONDS    (default: 3600)
set -euo pipefail

: "${CLOUDFLARE_API_TOKEN:?CLOUDFLARE_API_TOKEN must be set}"
: "${CLOUDFLARE_ACCOUNT_ID:?CLOUDFLARE_ACCOUNT_ID must be set}"
: "${TF_STATE_R2_ACCESS_KEY_ID:?TF_STATE_R2_ACCESS_KEY_ID must be set}"

bucket=${TF_STATE_R2_BUCKET:-playground-terraform-state}
prefix=${TF_STATE_R2_PREFIX:-exe/}
ttl=${TF_STATE_R2_TTL_SECONDS:-3600}
api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/r2/temp-access-credentials"

body=$(TF_STATE_R2_ACCESS_KEY_ID="$TF_STATE_R2_ACCESS_KEY_ID" \
  bucket="$bucket" prefix="$prefix" ttl="$ttl" python3 - <<'PY'
import json, os
print(json.dumps({
    "bucket": os.environ["bucket"],
    "parentAccessKeyId": os.environ["TF_STATE_R2_ACCESS_KEY_ID"],
    "permission": "object-read-write",
    "ttlSeconds": int(os.environ["ttl"]),
    "prefixes": [os.environ["prefix"]],
}))
PY
)

code=$(curl -sS -o /tmp/r2-temp-creds.json -w '%{http_code}' \
  -X POST \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  -H "Content-Type: application/json" \
  --data "$body" \
  "$api")

if [ "$code" != "200" ]; then
  echo "Minting R2 temporary credentials failed: HTTP ${code}" >&2
  cat /tmp/r2-temp-creds.json >&2 || true
  exit 1
fi

eval "$(python3 - <<'PY'
import json, shlex
data = json.load(open("/tmp/r2-temp-creds.json"))
if not data.get("success", False):
    raise SystemExit(f"Cloudflare API error: {data.get('errors')}")
result = data.get("result") or {}
for key, env in (
    ("accessKeyId", "AWS_ACCESS_KEY_ID"),
    ("secretAccessKey", "AWS_SECRET_ACCESS_KEY"),
    ("sessionToken", "AWS_SESSION_TOKEN"),
):
    val = result.get(key)
    if not val:
        raise SystemExit(f"missing {key} in temp-access-credentials response")
    print(f"export {env}={shlex.quote(val)}")
PY
)"

if [ -n "${GITHUB_ENV:-}" ]; then
  {
    echo "AWS_ACCESS_KEY_ID=${AWS_ACCESS_KEY_ID}"
    echo "AWS_SECRET_ACCESS_KEY=${AWS_SECRET_ACCESS_KEY}"
    echo "AWS_SESSION_TOKEN=${AWS_SESSION_TOKEN}"
  } >>"$GITHUB_ENV"
fi

# Keep temporary secrets out of Actions logs if a later step echoes env.
if [ -n "${GITHUB_ACTIONS:-}" ]; then
  echo "::add-mask::${AWS_ACCESS_KEY_ID}"
  echo "::add-mask::${AWS_SECRET_ACCESS_KEY}"
  echo "::add-mask::${AWS_SESSION_TOKEN}"
fi

echo "Minted R2 temporary credentials for bucket ${bucket} (prefix ${prefix}, ttl ${ttl}s)."

#!/usr/bin/env bash
# Mint short-lived R2 S3 credentials for Terraform state from CLOUDFLARE_API_TOKEN.
#
# Cloudflare maps an API token to S3 credentials as:
#   Access Key ID     = token id  (from /user/tokens/verify)
#   Secret Access Key = SHA-256 hex of the token value
# We use that Access Key ID as parentAccessKeyId for the Temporary Credentials
# API so Terraform never sees the long-lived secret. No separate
# TF_STATE_R2_* secrets are required.
#
# Writes AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, and AWS_SESSION_TOKEN to
# GITHUB_ENV when set (and exports them in this shell).
#
# Environment:
#   CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID
#   TF_STATE_R2_BUCKET         (default: playground-terraform-state)
#   TF_STATE_R2_PREFIX         Optional prefix scope (default: exe/)
#   TF_STATE_R2_TTL_SECONDS    (default: 3600)
set -euo pipefail

: "${CLOUDFLARE_API_TOKEN:?CLOUDFLARE_API_TOKEN must be set}"
: "${CLOUDFLARE_ACCOUNT_ID:?CLOUDFLARE_ACCOUNT_ID must be set}"

bucket=${TF_STATE_R2_BUCKET:-playground-terraform-state}
prefix=${TF_STATE_R2_PREFIX:-exe/}
ttl=${TF_STATE_R2_TTL_SECONDS:-3600}

# Resolve the token id (R2 Access Key ID) from the bearer token itself.
verify_code=$(curl -sS -o /tmp/cf-token-verify.json -w '%{http_code}' \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  "https://api.cloudflare.com/client/v4/user/tokens/verify")
if [ "$verify_code" != "200" ]; then
  echo "Verifying CLOUDFLARE_API_TOKEN failed: HTTP ${verify_code}" >&2
  cat /tmp/cf-token-verify.json >&2 || true
  exit 1
fi

parent_access_key_id=$(python3 - <<'PY'
import json
data = json.load(open("/tmp/cf-token-verify.json"))
if not data.get("success", False):
    raise SystemExit(f"Cloudflare verify error: {data.get('errors')}")
token_id = (data.get("result") or {}).get("id")
if not token_id:
    raise SystemExit("tokens/verify response missing result.id")
print(token_id, end="")
PY
)

api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/r2/temp-access-credentials"

# Write request body via a file so bash does not treat ')' inside Python as
# closing a $(...) substitution, and so we never need eval.
parent_access_key_id="$parent_access_key_id" \
  bucket="$bucket" prefix="$prefix" ttl="$ttl" python3 - <<'PY'
import json, os
from pathlib import Path

Path("/tmp/r2-temp-creds-body.json").write_text(json.dumps({
    "bucket": os.environ["bucket"],
    "parentAccessKeyId": os.environ["parent_access_key_id"],
    "permission": "object-read-write",
    "ttlSeconds": int(os.environ["ttl"]),
    "prefixes": [os.environ["prefix"]],
}))
PY

code=$(curl -sS -o /tmp/r2-temp-creds.json -w '%{http_code}' \
  -X POST \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  -H "Content-Type: application/json" \
  --data @/tmp/r2-temp-creds-body.json \
  "$api")

if [ "$code" != "200" ]; then
  echo "Minting R2 temporary credentials failed: HTTP ${code}" >&2
  cat /tmp/r2-temp-creds.json >&2 || true
  echo >&2
  echo "CLOUDFLARE_API_TOKEN must allow R2 Object Read & Write on bucket ${bucket}" \
    "(or Admin Read & Write), and Temporary Credentials on that account." >&2
  exit 1
fi

python3 - <<'PY'
import json
from pathlib import Path

data = json.load(open("/tmp/r2-temp-creds.json"))
if not data.get("success", False):
    raise SystemExit(f"Cloudflare API error: {data.get('errors')}")
result = data.get("result") or {}
for key, path in (
    ("accessKeyId", "/tmp/r2-aws-access-key-id"),
    ("secretAccessKey", "/tmp/r2-aws-secret-access-key"),
    ("sessionToken", "/tmp/r2-aws-session-token"),
):
    val = result.get(key)
    if not val:
        raise SystemExit(f"missing {key} in temp-access-credentials response")
    Path(path).write_text(val)
PY

AWS_ACCESS_KEY_ID=$(cat /tmp/r2-aws-access-key-id)
AWS_SECRET_ACCESS_KEY=$(cat /tmp/r2-aws-secret-access-key)
AWS_SESSION_TOKEN=$(cat /tmp/r2-aws-session-token)
export AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY AWS_SESSION_TOKEN
rm -f /tmp/cf-token-verify.json /tmp/r2-temp-creds-body.json \
  /tmp/r2-aws-access-key-id /tmp/r2-aws-secret-access-key /tmp/r2-aws-session-token

if [ -n "${GITHUB_ENV:-}" ]; then
  {
    echo "AWS_ACCESS_KEY_ID=${AWS_ACCESS_KEY_ID}"
    echo "AWS_SECRET_ACCESS_KEY=${AWS_SECRET_ACCESS_KEY}"
    echo "AWS_SESSION_TOKEN=${AWS_SESSION_TOKEN}"
  } >>"$GITHUB_ENV"
fi

if [ -n "${GITHUB_ACTIONS:-}" ]; then
  echo "::add-mask::${AWS_ACCESS_KEY_ID}"
  echo "::add-mask::${AWS_SECRET_ACCESS_KEY}"
  echo "::add-mask::${AWS_SESSION_TOKEN}"
fi

echo "Minted R2 temporary credentials for bucket ${bucket} (prefix ${prefix}, ttl ${ttl}s) from CLOUDFLARE_API_TOKEN."

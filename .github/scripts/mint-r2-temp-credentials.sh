#!/usr/bin/env bash
# Mint short-lived R2 S3 credentials for Terraform state from CLOUDFLARE_API_TOKEN.
#
# Cloudflare maps an API token to S3 credentials as:
#   Access Key ID     = token id
#   Secret Access Key = SHA-256 hex of the token value
#
# Token id comes from the Account or User verify endpoint (Workers tokens are
# usually Account API tokens, which 401 on /user/tokens/verify). We prefer the
# Temporary Credentials API so Terraform sees a short-lived session; if that
# fails, we fall back to the derived Access Key ID / Secret for this job.
#
# Writes AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, and optionally
# AWS_SESSION_TOKEN to GITHUB_ENV when set (and exports them in this shell).
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

# Account API tokens (typical for Workers) verify here; User tokens use /user/...
verify_urls=(
  "https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/tokens/verify"
  "https://api.cloudflare.com/client/v4/user/tokens/verify"
)

parent_access_key_id=""
for url in "${verify_urls[@]}"; do
  verify_code=$(curl -sS -o /tmp/cf-token-verify.json -w '%{http_code}' \
    -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
    "$url" || true)
  if [ "$verify_code" = "200" ]; then
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
    echo "Resolved CLOUDFLARE_API_TOKEN via ${url}"
    break
  fi
done

if [ -z "$parent_access_key_id" ]; then
  echo "Verifying CLOUDFLARE_API_TOKEN failed on account and user endpoints." >&2
  cat /tmp/cf-token-verify.json >&2 || true
  exit 1
fi

api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/r2/temp-access-credentials"

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

use_session=0
if [ "$code" = "200" ]; then
  if python3 - <<'PY'
import json
from pathlib import Path

data = json.load(open("/tmp/r2-temp-creds.json"))
if not data.get("success", False):
    raise SystemExit(1)
result = data.get("result") or {}
for key, path in (
    ("accessKeyId", "/tmp/r2-aws-access-key-id"),
    ("secretAccessKey", "/tmp/r2-aws-secret-access-key"),
    ("sessionToken", "/tmp/r2-aws-session-token"),
):
    val = result.get(key)
    if not val:
        raise SystemExit(1)
    Path(path).write_text(val)
PY
  then
    use_session=1
  fi
fi

if [ "$use_session" -eq 1 ]; then
  AWS_ACCESS_KEY_ID=$(cat /tmp/r2-aws-access-key-id)
  AWS_SECRET_ACCESS_KEY=$(cat /tmp/r2-aws-secret-access-key)
  AWS_SESSION_TOKEN=$(cat /tmp/r2-aws-session-token)
  export AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY AWS_SESSION_TOKEN
  cred_kind="temporary session"
else
  echo "Temporary credentials API returned HTTP ${code}; falling back to token-derived S3 keys." >&2
  cat /tmp/r2-temp-creds.json >&2 || true
  # Access Key ID = token id; Secret = SHA-256 of token value (Cloudflare R2 docs).
  AWS_ACCESS_KEY_ID="$parent_access_key_id"
  AWS_SECRET_ACCESS_KEY=$(printf '%s' "$CLOUDFLARE_API_TOKEN" | openssl dgst -sha256 -hex | awk '{print $2}')
  unset AWS_SESSION_TOKEN || true
  export AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY
  cred_kind="token-derived"
fi

rm -f /tmp/cf-token-verify.json /tmp/r2-temp-creds-body.json \
  /tmp/r2-aws-access-key-id /tmp/r2-aws-secret-access-key /tmp/r2-aws-session-token

if [ -n "${GITHUB_ENV:-}" ]; then
  {
    echo "AWS_ACCESS_KEY_ID=${AWS_ACCESS_KEY_ID}"
    echo "AWS_SECRET_ACCESS_KEY=${AWS_SECRET_ACCESS_KEY}"
    if [ -n "${AWS_SESSION_TOKEN:-}" ]; then
      echo "AWS_SESSION_TOKEN=${AWS_SESSION_TOKEN}"
    fi
  } >>"$GITHUB_ENV"
fi

if [ -n "${GITHUB_ACTIONS:-}" ]; then
  echo "::add-mask::${AWS_ACCESS_KEY_ID}"
  echo "::add-mask::${AWS_SECRET_ACCESS_KEY}"
  if [ -n "${AWS_SESSION_TOKEN:-}" ]; then
    echo "::add-mask::${AWS_SESSION_TOKEN}"
  fi
fi

echo "Exported ${cred_kind} R2 S3 credentials for bucket ${bucket} (prefix ${prefix})."

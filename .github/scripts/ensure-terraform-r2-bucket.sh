#!/usr/bin/env bash
# Ensure the Cloudflare R2 bucket used for Terraform state exists.
#
# Environment:
#   CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID
#   TF_STATE_R2_BUCKET  (default: playground-terraform-state)
set -euo pipefail

: "${CLOUDFLARE_API_TOKEN:?CLOUDFLARE_API_TOKEN must be set}"
: "${CLOUDFLARE_ACCOUNT_ID:?CLOUDFLARE_ACCOUNT_ID must be set}"

bucket=${TF_STATE_R2_BUCKET:-playground-terraform-state}
api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/r2/buckets"

code=$(curl -sS -o /tmp/r2-bucket-list.json -w '%{http_code}' \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  "${api}?per_page=100")
if [ "$code" != "200" ]; then
  echo "Listing R2 buckets failed: HTTP ${code}" >&2
  cat /tmp/r2-bucket-list.json >&2 || true
  exit 1
fi

if python3 - "$bucket" <<'PY'
import json, sys
name = sys.argv[1]
data = json.load(open("/tmp/r2-bucket-list.json"))
buckets = (data.get("result") or {}).get("buckets") or []
sys.exit(0 if any(b.get("name") == name for b in buckets) else 1)
PY
then
  echo "R2 bucket ${bucket} already exists."
  exit 0
fi

echo "Creating R2 bucket ${bucket}..."
code=$(curl -sS -o /tmp/r2-bucket-create.json -w '%{http_code}' \
  -X POST \
  -H "Authorization: Bearer ${CLOUDFLARE_API_TOKEN}" \
  -H "Content-Type: application/json" \
  --data "{\"name\":\"${bucket}\"}" \
  "$api")
if [ "$code" != "200" ] && [ "$code" != "201" ]; then
  # 409 = already exists (race with another job)
  if [ "$code" = "409" ]; then
    echo "R2 bucket ${bucket} already exists (conflict)."
    exit 0
  fi
  echo "Creating R2 bucket failed: HTTP ${code}" >&2
  cat /tmp/r2-bucket-create.json >&2 || true
  exit 1
fi

echo "Created R2 bucket ${bucket}."

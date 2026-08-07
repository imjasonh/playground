#!/usr/bin/env bash
# Offline shell validation for rotation tooling and runbook ordering.
set -euo pipefail
set +x
umask 077

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUNBOOK="$ROOT/docs/key-rotation-runbook.md"

for script in \
  "$ROOT/hack/inspect-control-pki.sh" \
  "$ROOT/hack/inspect-rotation-state.sh" \
  "$ROOT/hack/inspect-terraform-backend.sh"; do
  bash -n "$script"
done

for command in jq openssl ssh-keygen; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "required command not found: $command" >&2
    exit 1
  }
done

tmp="$(mktemp -d "${TMPDIR:-/tmp}/sshcloud-rotation-test.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
fixtures="$tmp/fixtures"
fakebin="$tmp/bin"
tfdir="$tmp/terraform"
mkdir -p "$fixtures" "$fakebin" "$tfdir/.terraform"

make_ca() {
  local slot="$1"
  openssl ecparam -name prime256v1 -genkey -noout -out "$tmp/ca-$slot.key"
  openssl req -new -x509 \
    -key "$tmp/ca-$slot.key" \
    -sha256 \
    -days 3650 \
    -subj "/CN=fixture-control-ca-$slot" \
    -addext "basicConstraints=critical,CA:TRUE" \
    -addext "keyUsage=critical,keyCertSign,cRLSign,digitalSignature" \
    -out "$fixtures/fixture-control-ca-$slot"
}
make_ca a
make_ca b

roles=(gateway orchestrator agent snapshot)
for role in "${roles[@]}"; do
  uri="spiffe://sshcloud.internal/control/$role"
  openssl ecparam -name prime256v1 -genkey -noout -out "$tmp/$role.key"
  openssl req -new \
    -key "$tmp/$role.key" \
    -subj "/CN=fixture-$role" \
    -out "$tmp/$role.csr"
  cat >"$tmp/$role.ext" <<EOF
subjectAltName=URI:$uri,DNS:$role.control.sshcloud.internal
extendedKeyUsage=serverAuth,clientAuth
keyUsage=digitalSignature
EOF
  openssl x509 -req \
    -in "$tmp/$role.csr" \
    -CA "$fixtures/fixture-control-ca-a" \
    -CAkey "$tmp/ca-a.key" \
    -CAcreateserial \
    -sha256 \
    -days 90 \
    -extfile "$tmp/$role.ext" \
    -out "$tmp/$role.crt" >/dev/null 2>&1
  jq -n \
    --rawfile certificate_pem "$tmp/$role.crt" \
    --rawfile private_key_pem "$tmp/$role.key" \
    --arg uri_identity "$uri" \
    '{certificate_pem: $certificate_pem, private_key_pem: $private_key_pem, uri_identity: $uri_identity}' \
    >"$fixtures/fixture-control-identity-$role"
done

ssh-keygen -q -t ed25519 -N '' -C fixture-gateway-secret -f "$fixtures/fixture-gateway-host-key"
rm -f "$fixtures/fixture-gateway-host-key.pub"
ssh-keygen -q -t ed25519 -N '' -C fixture-user-ca-secret -f "$fixtures/fixture-user-ca"
ssh-keygen -y -f "$fixtures/fixture-user-ca" >"$fixtures/fixture-user-ca-pub"
policy_key="$(cat "$fixtures/fixture-user-ca-pub")"
jq -n \
  --arg key "$policy_key TOP-SECRET-COMMENT" \
  '{
    version: 1,
    join_mode: "allowlist",
    deploy_mode: "allowlist",
    member_ssh_public_keys: [$key],
    deployer_ssh_public_keys: [$key]
  }' >"$fixtures/fixture-access-policy"

cat >"$fakebin/gcloud" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
fixtures="${ROTATION_FIXTURES:?}"
args=" $* "

value_for() {
  local name="$1" arg
  for arg in "$@"; do
    if [[ "$arg" == "--$name="* ]]; then
      printf '%s' "${arg#*=}"
      return
    fi
  done
  return 1
}

if [[ "$args" == *" secrets versions list "* ]]; then
  secret="$4"
  printf '[{"name":"projects/fixture/secrets/%s/versions/1","state":"ENABLED","createTime":"2026-01-01T00:00:00Z"}]\n' "$secret"
elif [[ "$args" == *" secrets versions access latest "* ]]; then
  secret="$(value_for secret "$@")"
  out="$(value_for out-file "$@")"
  cp "$fixtures/$secret" "$out"
elif [[ "$args" == *" kms keys describe "* ]]; then
  key="$4"
  cat <<JSON
{"name":"projects/fixture/locations/test/keyRings/fixture-snapshots/cryptoKeys/$key","purpose":"ENCRYPT_DECRYPT","primary":{"name":"projects/fixture/locations/test/keyRings/fixture-snapshots/cryptoKeys/$key/cryptoKeyVersions/2"}}
JSON
elif [[ "$args" == *" kms keys versions list "* ]]; then
  key="$(value_for key "$@")"
  cat <<JSON
[
  {"name":"projects/fixture/locations/test/keyRings/fixture-snapshots/cryptoKeys/$key/cryptoKeyVersions/1","state":"ENABLED","createTime":"2026-01-01T00:00:00Z"},
  {"name":"projects/fixture/locations/test/keyRings/fixture-snapshots/cryptoKeys/$key/cryptoKeyVersions/2","state":"ENABLED","createTime":"2026-02-01T00:00:00Z"}
]
JSON
elif [[ "$args" == *" storage buckets describe "* ]]; then
  cat <<JSON
{
  "name": "fixture-state",
  "projectNumber": "${FIXTURE_BUCKET_PROJECT_NUMBER:-123456789}",
  "versioning": {"enabled": true},
  "iamConfiguration": {
    "uniformBucketLevelAccess": {"enabled": true},
    "publicAccessPrevention": "enforced"
  },
  "retentionPolicy": {"retentionPeriod": "${FIXTURE_BUCKET_RETENTION_SECONDS:-0}"},
  "softDeletePolicy": {"retentionDurationSeconds": "${FIXTURE_BUCKET_SOFT_DELETE_SECONDS:-604800}"},
  "encryption": {"defaultKmsKeyName": "projects/fixture/locations/test/keyRings/state/cryptoKeys/state"}
}
JSON
elif [[ "$args" == *" storage buckets get-iam-policy "* ]]; then
  cat <<'JSON'
{"bindings":[{"role":"roles/storage.objectAdmin","members":["serviceAccount:fixture@example.invalid"]}]}
JSON
elif [[ "$args" == *" projects describe fixture "* ]]; then
  printf '123456789\n'
else
  echo "unexpected fake gcloud invocation" >&2
  exit 90
fi
EOF
chmod 0700 "$fakebin/gcloud"

cat >"$fakebin/ssh-keyscan" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
pub="$(ssh-keygen -y -f "${ROTATION_FIXTURES:?}/fixture-gateway-host-key")"
printf 'fixture.example %s\n' "$pub"
EOF
chmod 0700 "$fakebin/ssh-keyscan"

cat >"$tfdir/versions.tf" <<'EOF'
terraform {
  backend "gcs" {}
}
EOF
cat >"$tfdir/.gitignore" <<'EOF'
*.tfstate
*.tfstate.*
EOF
cat >"$tfdir/.terraform/terraform.tfstate" <<'EOF'
{
  "version": 3,
  "backend": {
    "type": "gcs",
    "config": {
      "bucket": "fixture-state",
      "prefix": "fixture"
    }
  },
  "resources": [{"fixture_secret": "STATE-SECRET-SENTINEL"}]
}
EOF

output="$tmp/output"
ROTATION_FIXTURES="$fixtures" \
  PATH="$fakebin:$PATH" \
  "$ROOT/hack/inspect-rotation-state.sh" \
  --project fixture \
  --region test \
  --prefix fixture \
  --active-ca-slot a \
  --terraform-dir "$tfdir" \
  --gateway-host fixture.example >"$output" 2>&1

for required in \
  'control_ca slot=a usage=active' \
  'control_leaf role=gateway uri=spiffe://sshcloud.internal/control/gateway issuer_slot=a' \
  'gateway_host_key source=live' \
  'platform_user_ca fingerprint=SHA256:' \
  'access_policy version=1 join_mode=allowlist deploy_mode=allowlist' \
  'kms_key key=snapshot-envelope primary_version=2' \
  'terraform_backend configured=gcs initialized=gcs'; do
  if ! grep -Fq "$required" "$output"; then
    echo "rotation inspector output is missing: $required" >&2
    exit 1
  fi
done

if grep -Eq -- 'BEGIN .*PRIVATE KEY|TOP-SECRET-COMMENT|STATE-SECRET-SENTINEL|fixture-(gateway|user)-ca-secret' "$output"; then
  echo "rotation inspector emitted secret material or key comments" >&2
  exit 1
fi

for unsafe in project_mismatch retention_lock missing_soft_delete; do
  case "$unsafe" in
    project_mismatch)
      unsafe_env=(FIXTURE_BUCKET_PROJECT_NUMBER=987654321)
      ;;
    retention_lock)
      unsafe_env=(FIXTURE_BUCKET_RETENTION_SECONDS=3600)
      ;;
    missing_soft_delete)
      unsafe_env=(FIXTURE_BUCKET_SOFT_DELETE_SECONDS=0)
      ;;
  esac
  if env \
    ROTATION_FIXTURES="$fixtures" \
    PATH="$fakebin:$PATH" \
    "${unsafe_env[@]}" \
    "$ROOT/hack/inspect-terraform-backend.sh" \
    --terraform-dir "$tfdir" \
    --project fixture >"$tmp/backend-$unsafe" 2>&1; then
    echo "backend inspector accepted unsafe fixture: $unsafe" >&2
    exit 1
  fi
done

for private_file in \
  "$fixtures/fixture-gateway-host-key" \
  "$fixtures/fixture-user-ca" \
  "$tmp/gateway.key"; do
  [[ -f "$private_file" ]] || continue
  sentinel="$(sed -n '2p' "$private_file")"
  if [[ -n "$sentinel" ]] && grep -Fq "$sentinel" "$output"; then
    echo "rotation inspector emitted private key bytes" >&2
    exit 1
  fi
done

line_number() {
  local text="$1"
  grep -nF "$text" "$RUNBOOK" | head -n 1 | cut -d: -f1
}

assert_order() {
  local previous=0 text line
  for text in "$@"; do
    line="$(line_number "$text")"
    if [[ -z "$line" || "$line" -le "$previous" ]]; then
      echo "runbook ordering is missing or invalid at: $text" >&2
      exit 1
    fi
    previous="$line"
  done
}

assert_order \
  '### Stage 0: establish the baseline' \
  '### Stage 1: replace only idle CA B' \
  '### Stage 2: issue leaves under B' \
  '### Stage 3: prove A is idle, then refresh it'
assert_order \
  '## Gateway SSH host-key rotation' \
  'Set `ssh_client_cidrs = []`' \
  'Increment only `gateway_host_key_rotation_epoch`' \
  'containing both old and new entries' \
  'Reset/reboot the gateway VM' \
  'Restore only the approved `/32` ingress'
assert_order \
  '## Platform SSH user-CA rotation' \
  'trusting old + next simultaneously' \
  'switch the gateway signer' \
  'Wait longer than the maximum user-certificate TTL' \
  'trusting only the new CA' \
  'disable and later destroy the old signing-key'
assert_order \
  '## Secret Manager version cleanup' \
  'Map every consumer and mounted fingerprint' \
  'Disable the old numbered version' \
  'Wait through the secret-specific retention' \
  'Destroy the numbered version'
assert_order \
  '### Backend bootstrap and migration' \
  'Freeze applies, then make a private pre-migration backup' \
  'Migrate:' \
  'Pull a post-migration backup'

if ! grep -Fq \
  'create → enable/verify → set primary → prove new writes → migrate/expire all' \
  "$RUNBOOK"; then
  echo "runbook must preserve KMS create/primary/migrate/disable/destroy ordering" >&2
  exit 1
fi
if [[ "$(grep -c 'early_renewal_hours   = 0' "$ROOT/terraform/secrets.tf")" -ne 2 ]] ||
  grep -Eq 'early_renewal_hours[[:space:]]*=[[:space:]]*[1-9]' "$ROOT/terraform/secrets.tf"; then
  echo "new control certificates must disable time-triggered early renewal" >&2
  exit 1
fi
if [[ "$(grep -c 'deletion_policy = "ABANDON"' "$ROOT/terraform/secrets.tf")" -lt 6 ]]; then
  echo "all rotating Secret Manager resources must retain superseded versions" >&2
  exit 1
fi
for required in \
  'variable "control_ca_rotation_epochs"' \
  'variable "control_leaf_rotation_epochs"' \
  'variable "gateway_host_key_rotation_epoch"'; do
  grep -Fq "$required" "$ROOT/terraform/variables.tf" || {
    echo "missing deterministic rotation input: $required" >&2
    exit 1
  }
done
for moved_target in \
  'tls_private_key.gateway_host["0"]' \
  'tls_private_key.control_ca["a-0"]' \
  'tls_private_key.control_ca["b-0"]' \
  'tls_private_key.control_role["gateway-0"]' \
  'tls_private_key.control_role["orchestrator-0"]' \
  'tls_private_key.control_role["agent-0"]' \
  'tls_private_key.control_role["snapshot-0"]'; do
  grep -Fq "$moved_target" "$ROOT/terraform/secrets.tf" || {
    echo "missing migration-safe epoch-zero state move: $moved_target" >&2
    exit 1
  }
done
grep -Fq 'backend "gcs" {}' "$ROOT/terraform/versions.tf" || {
  echo "Terraform must require an operator-configured GCS backend" >&2
  exit 1
}

echo "key-rotation tooling checks passed"

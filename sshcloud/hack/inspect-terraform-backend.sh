#!/usr/bin/env bash
# Inspect backend metadata and bucket controls without reading Terraform state.
set -euo pipefail
set +x
umask 077

usage() {
  cat <<'EOF'
Usage: inspect-terraform-backend.sh [options]

Options:
  --terraform-dir DIR  Terraform root (default: ../terraform)
  --project PROJECT    GCP project used to describe an initialized GCS backend

The script never runs terraform state pull/show/output and never queries or
prints resource instances. For a GCS backend it selects only backend fields
from Terraform's local metadata plus bucket configuration/IAM, reporting
counts rather than members.
It exits nonzero for local, uninitialized, mismatched, public, or incompletely
protected backends. Bucket IAM cannot prove the absence of inherited
project/folder/organization access; that remains a manual review.
EOF
}

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
terraform_dir="$ROOT/terraform"
project=""

while (($#)); do
  case "$1" in
    --terraform-dir)
      terraform_dir="${2:?missing value for --terraform-dir}"
      shift 2
      ;;
    --project)
      project="${2:?missing value for --project}"
      shift 2
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[[ -d "$terraform_dir" ]] || {
  echo "Terraform directory does not exist" >&2
  exit 2
}
command -v jq >/dev/null 2>&1 || {
  echo "required command not found: jq" >&2
  exit 1
}

shopt -s nullglob
terraform_files=("$terraform_dir"/*.tf)
shopt -u nullglob
if [[ "${#terraform_files[@]}" -eq 0 ]]; then
  echo "Terraform directory contains no .tf files" >&2
  exit 2
fi
configured_backends="$(
  sed -n 's/^[[:space:]]*backend[[:space:]]*"\([^"]*\)".*/\1/p' \
    "${terraform_files[@]}" |
    sort -u
)"
configured_count="$(printf '%s\n' "$configured_backends" | sed '/^$/d' | wc -l)"
if [[ "$configured_count" -eq 0 ]]; then
  configured_backend="local-default"
elif [[ "$configured_count" -eq 1 ]]; then
  configured_backend="$configured_backends"
else
  printf 'terraform_backend configured=invalid initialized=unknown safety=fail reason=multiple_backend_blocks\n'
  exit 1
fi

metadata="$terraform_dir/.terraform/terraform.tfstate"
initialized_backend="uninitialized"
bucket=""
prefix=""
if [[ -f "$metadata" ]]; then
  initialized_backend="$(jq -er '.backend.type // "local"' "$metadata")"
  if [[ "$initialized_backend" == "gcs" ]]; then
    bucket="$(jq -er '.backend.config.bucket' "$metadata")"
    prefix="$(jq -r '.backend.config.prefix // ""' "$metadata")"
    sensitive_backend_keys="$(
      jq -r '
        .backend.config
        | to_entries
        | map(select(
            (.key == "access_token" or
             .key == "credentials" or
             .key == "encryption_key") and
            (.value != null and .value != "")
          ))
        | map(.key)
        | join(",")
      ' "$metadata"
    )"
    if [[ -n "$sensitive_backend_keys" ]]; then
      printf 'terraform_backend configured=%s initialized=%s safety=fail reason=sensitive_backend_config_present keys=%s\n' \
        "$configured_backend" "$initialized_backend" "$sensitive_backend_keys"
      exit 1
    fi
  fi
fi

local_state_count=0
local_state_unsafe=0
shopt -s nullglob
state_files=("$terraform_dir"/*.tfstate "$terraform_dir"/*.tfstate.*)
shopt -u nullglob
for state_file in "${state_files[@]}"; do
  [[ -f "$state_file" ]] || continue
  local_state_count=$((local_state_count + 1))
  mode="$(stat -c '%a' "$state_file" 2>/dev/null || stat -f '%Lp' "$state_file")"
  ignored="unknown"
  if command -v git >/dev/null 2>&1; then
    ignored="no"
    git -C "$terraform_dir" check-ignore -q "$(basename "$state_file")" && ignored="yes"
  fi
  printf 'local_state_file name=%s mode=%s git_ignored=%s\n' \
    "$(basename "$state_file")" "$mode" "$ignored"
  # A remote backend should leave no working state copy behind, even if the
  # copy is mode 0600 and git-ignored.
  local_state_unsafe=1
done

if [[ "$configured_backend" != "gcs" ]]; then
  printf 'terraform_backend configured=%s initialized=%s local_state_files=%s safety=fail reason=remote_gcs_backend_not_configured\n' \
    "$configured_backend" "$initialized_backend" "$local_state_count"
  exit 1
fi
if [[ "$initialized_backend" == "uninitialized" ]]; then
  printf 'terraform_backend configured=gcs initialized=uninitialized local_state_files=%s safety=fail reason=run_reviewed_state_migration\n' \
    "$local_state_count"
  exit 1
fi
if [[ "$initialized_backend" != "gcs" ]]; then
  printf 'terraform_backend configured=gcs initialized=%s local_state_files=%s safety=fail reason=backend_mismatch\n' \
    "$initialized_backend" "$local_state_count"
  exit 1
fi
if [[ -z "$bucket" || -z "$prefix" ]]; then
  printf 'terraform_backend configured=gcs initialized=gcs local_state_files=%s safety=fail reason=dedicated_bucket_and_prefix_required\n' \
    "$local_state_count"
  exit 1
fi
if ((local_state_unsafe)); then
  printf 'terraform_backend configured=gcs initialized=gcs bucket=%s prefix=%q local_state_files=%s safety=fail reason=unsafe_local_state_copy\n' \
    "$bucket" "$prefix" "$local_state_count"
  exit 1
fi

command -v gcloud >/dev/null 2>&1 || {
  echo "required command not found: gcloud" >&2
  exit 1
}
bucket_json="$(mktemp "${TMPDIR:-/tmp}/sshcloud-state-bucket.XXXXXX")"
iam_json="$(mktemp "${TMPDIR:-/tmp}/sshcloud-state-iam.XXXXXX")"
trap 'rm -f "$bucket_json" "$iam_json"' EXIT
project_args=()
[[ -n "$project" ]] && project_args=(--project="$project")
gcloud storage buckets describe "gs://$bucket" \
  "${project_args[@]}" \
  --format=json >"$bucket_json"
gcloud storage buckets get-iam-policy "gs://$bucket" \
  "${project_args[@]}" \
  --format=json >"$iam_json"

versioning="$(jq -r '.versioning.enabled // false' "$bucket_json")"
ubla="$(jq -r '.iamConfiguration.uniformBucketLevelAccess.enabled // false' "$bucket_json")"
pap="$(jq -r '.iamConfiguration.publicAccessPrevention // "unspecified"' "$bucket_json")"
retention_seconds="$(jq -r '.retentionPolicy.retentionPeriod // 0' "$bucket_json")"
soft_delete_seconds="$(jq -r '.softDeletePolicy.retentionDurationSeconds // 0' "$bucket_json")"
cmek="no"
[[ "$(jq -r '.encryption.defaultKmsKeyName // ""' "$bucket_json")" != "" ]] && cmek="yes"
public_bindings="$(jq -r '
  [
    .bindings[]?
    | select(any(.members[]?; . == "allUsers" or . == "allAuthenticatedUsers"))
  ]
  | length
' "$iam_json")"
binding_count="$(jq -r '[.bindings[]?] | length' "$iam_json")"
admin_binding_count="$(jq -r '[.bindings[]? | select(.role == "roles/storage.admin")] | length' "$iam_json")"

safety="pass"
reason="protected_gcs_backend"
if [[ "$versioning" != "true" ||
  "$ubla" != "true" ||
  "$pap" != "enforced" ||
  "$public_bindings" != "0" ||
  "$admin_binding_count" != "0" ||
  ( "$retention_seconds" == "0" && "$soft_delete_seconds" == "0" ) ]]; then
  safety="fail"
  reason="bucket_controls_incomplete"
fi

printf 'terraform_backend configured=gcs initialized=gcs bucket=%s prefix=%q locking=gcs-native local_state_files=%s safety=%s reason=%s\n' \
  "$bucket" "$prefix" "$local_state_count" "$safety" "$reason"
printf 'terraform_backend_bucket versioning=%s uniform_access=%s public_access_prevention=%s retention_seconds=%s soft_delete_seconds=%s cmek=%s public_bindings=%s iam_bindings=%s admin_bindings=%s\n' \
  "$versioning" \
  "$ubla" \
  "$pap" \
  "$retention_seconds" \
  "$soft_delete_seconds" \
  "$cmek" \
  "$public_bindings" \
  "$binding_count" \
  "$admin_binding_count"

[[ "$safety" == "pass" ]]

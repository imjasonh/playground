#!/usr/bin/env bash
# Read-only GCP/key-rotation inventory. Secret payloads are parsed in a private
# temporary directory and are never written to stdout or stderr.
set -euo pipefail
set +x
umask 077

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
  cat <<'EOF'
Usage: inspect-rotation-state.sh --project PROJECT --region REGION [options]

Options:
  --prefix NAME         Resource prefix (default: sshcloud)
  --active-ca-slot a|b  Configured control leaf-signing slot (required)
  --terraform-dir DIR   Terraform directory (default: sshcloud/terraform)
  --gateway-host HOST   Also compare the live gateway Ed25519 host key
  --gateway-port PORT   Gateway SSH port (default: 22)

Required tools: gcloud, jq, openssl, ssh-keygen. ssh-keyscan is additionally
required with --gateway-host. The caller needs metadata/list access plus Secret
Manager payload access to the named sshcloud secrets. The script performs no
create, update, disable, destroy, IAM, or Terraform state operation.
EOF
}

project=""
region=""
prefix="sshcloud"
active_slot=""
terraform_dir="$ROOT/terraform"
gateway_host=""
gateway_port="22"

while (($#)); do
  case "$1" in
    --project)
      project="${2:?missing value for --project}"
      shift 2
      ;;
    --region)
      region="${2:?missing value for --region}"
      shift 2
      ;;
    --prefix)
      prefix="${2:?missing value for --prefix}"
      shift 2
      ;;
    --active-ca-slot)
      active_slot="${2:?missing value for --active-ca-slot}"
      shift 2
      ;;
    --terraform-dir)
      terraform_dir="${2:?missing value for --terraform-dir}"
      shift 2
      ;;
    --gateway-host)
      gateway_host="${2:?missing value for --gateway-host}"
      shift 2
      ;;
    --gateway-port)
      gateway_port="${2:?missing value for --gateway-port}"
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

[[ -n "$project" ]] || {
  echo "--project is required" >&2
  exit 2
}
[[ -n "$region" ]] || {
  echo "--region is required" >&2
  exit 2
}
[[ "$prefix" =~ ^[a-z][a-z0-9-]{0,40}$ ]] || {
  echo "--prefix must contain only lowercase letters, digits, and hyphens" >&2
  exit 2
}
case "$active_slot" in
  a | b) ;;
  *)
    echo "--active-ca-slot must be a or b" >&2
    exit 2
    ;;
esac
[[ "$gateway_port" =~ ^[0-9]+$ ]] && ((gateway_port >= 1 && gateway_port <= 65535)) || {
  echo "--gateway-port must be between 1 and 65535" >&2
  exit 2
}

for command in gcloud jq openssl ssh-keygen; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "required command not found: $command" >&2
    exit 1
  }
done
if [[ -n "$gateway_host" ]]; then
  command -v ssh-keyscan >/dev/null 2>&1 || {
    echo "required command not found: ssh-keyscan" >&2
    exit 1
  }
fi

tmp="$(mktemp -d "${TMPDIR:-/tmp}/sshcloud-rotation-inspect.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

access_secret() {
  local secret="$1" out="$2"
  if ! gcloud secrets versions access latest \
    --secret="$secret" \
    --project="$project" \
    --out-file="$out" >/dev/null; then
    echo "unable to inspect latest version metadata for secret $secret" >&2
    return 1
  fi
  chmod 0600 "$out"
}

list_secret_versions() {
  local secret="$1" listing="$tmp/versions-$secret.json"
  gcloud secrets versions list "$secret" \
    --project="$project" \
    --format=json >"$listing"
  jq -er --arg secret "$secret" '
    . as $versions
    | ($versions | map(.name | split("/")[-1] | tonumber) | max) as $latest
    | $versions[]
    | [
        $secret,
        (.name | split("/")[-1]),
        (if (.name | split("/")[-1] | tonumber) == $latest then "yes" else "no" end),
        .state,
        (.createTime // "-"),
        (.destroyTime // "-")
      ]
    | @tsv
  ' "$listing" |
    while IFS=$'\t' read -r name version latest state created destroyed; do
      printf 'secret_version secret=%s version=%s latest=%s state=%s created=%q destroyed=%q\n' \
        "$name" "$version" "$latest" "$state" "$created" "$destroyed"
    done
}

control_ca_a="${prefix}-control-ca-a"
control_ca_b="${prefix}-control-ca-b"
access_policy="${prefix}-access-policy"
gateway_host_key="${prefix}-gateway-host-key"
user_ca="${prefix}-user-ca"
user_ca_pub="${prefix}-user-ca-pub"
roles=(gateway orchestrator agent snapshot)
secrets=(
  "$control_ca_a"
  "$control_ca_b"
  "$access_policy"
  "$gateway_host_key"
  "$user_ca"
  "$user_ca_pub"
)
for role in "${roles[@]}"; do
  secrets+=("${prefix}-control-identity-${role}")
done

printf '%s\n' '== Secret Manager version states =='
for secret in "${secrets[@]}"; do
  list_secret_versions "$secret"
done

access_secret "$control_ca_a" "$tmp/ca-a.pem"
access_secret "$control_ca_b" "$tmp/ca-b.pem"

printf '%s\n' '== Control CA and role-certificate metadata =='
"$ROOT/hack/inspect-control-pki.sh" \
  --active-slot "$active_slot" \
  --ca-a "$tmp/ca-a.pem" \
  --ca-b "$tmp/ca-b.pem" \
  --mode ca

for role in "${roles[@]}"; do
  bundle="$tmp/identity-$role.json"
  cert="$tmp/identity-$role.crt"
  key="$tmp/identity-$role.key"
  access_secret "${prefix}-control-identity-${role}" "$bundle"
  jq -er '
    type == "object"
    and (.certificate_pem | type == "string" and length > 0)
    and (.private_key_pem | type == "string" and length > 0)
    and (.uri_identity | type == "string" and length > 0)
  ' "$bundle" >/dev/null || {
    echo "control identity $role has an invalid bundle shape" >&2
    exit 1
  }
  jq -er .certificate_pem "$bundle" >"$cert"
  jq -er .private_key_pem "$bundle" >"$key"
  expected_uri="spiffe://sshcloud.internal/control/$role"
  if [[ "$(jq -er .uri_identity "$bundle")" != "$expected_uri" ]]; then
    echo "control identity $role declares an unexpected URI identity" >&2
    exit 1
  fi
  chmod 0600 "$cert" "$key"
  "$ROOT/hack/inspect-control-pki.sh" \
    --active-slot "$active_slot" \
    --expected-role "$role" \
    --ca-a "$tmp/ca-a.pem" \
    --ca-b "$tmp/ca-b.pem" \
    --cert "$cert" \
    --key "$key" \
    --mode leaf
done

ssh_fingerprint() {
  local file="$1"
  ssh-keygen -E sha256 -lf "$file" 2>/dev/null | awk '{print $2}'
}

printf '%s\n' '== SSH host and platform user-CA fingerprints =='
access_secret "$gateway_host_key" "$tmp/gateway-host-private"
ssh-keygen -y -f "$tmp/gateway-host-private" >"$tmp/gateway-host-public"
gateway_expected_fp="$(ssh_fingerprint "$tmp/gateway-host-public")"
printf 'gateway_host_key source=secret-manager-latest fingerprint=%s\n' "$gateway_expected_fp"

if [[ -n "$gateway_host" ]]; then
  if ! ssh-keyscan -T 5 -p "$gateway_port" -t ed25519 "$gateway_host" \
    >"$tmp/gateway-live-public" 2>/dev/null; then
    echo "unable to scan the live gateway host key" >&2
    exit 1
  fi
  gateway_live_fp="$(ssh_fingerprint "$tmp/gateway-live-public")"
  gateway_match="no"
  [[ "$gateway_live_fp" == "$gateway_expected_fp" ]] && gateway_match="yes"
  printf 'gateway_host_key source=live fingerprint=%s latest_secret_match=%s\n' \
    "$gateway_live_fp" "$gateway_match"
fi

access_secret "$user_ca" "$tmp/user-ca-private"
access_secret "$user_ca_pub" "$tmp/user-ca-public"
ssh-keygen -y -f "$tmp/user-ca-private" >"$tmp/user-ca-derived-public"
user_ca_private_fp="$(ssh_fingerprint "$tmp/user-ca-derived-public")"
user_ca_public_fp="$(ssh_fingerprint "$tmp/user-ca-public")"
user_ca_match="no"
[[ "$user_ca_private_fp" == "$user_ca_public_fp" ]] && user_ca_match="yes"
printf 'platform_user_ca fingerprint=%s public_secret_match=%s\n' \
  "$user_ca_private_fp" "$user_ca_match"

inspect_policy_keys() {
  local field="$1" label="$2" policy_file="$3"
  local count index=0 key_file="$tmp/policy-key"
  count="$(jq -er --arg field "$field" '.[$field] | length' "$policy_file")"
  printf 'access_policy_keys set=%s count=%s\n' "$label" "$count"
  while IFS= read -r key_line; do
    printf '%s\n' "$key_line" >"$key_file"
    if ! fingerprint="$(ssh_fingerprint "$key_file")"; then
      echo "access policy contains an invalid $label key at index $index" >&2
      exit 1
    fi
    key_type="$(awk 'NR == 1 { print $1 }' "$key_file")"
    case "$key_type" in
      ssh-* | ecdsa-* | sk-*) ;;
      *)
        echo "access policy $label key at index $index has options or an invalid key type" >&2
        exit 1
        ;;
    esac
    printf 'access_policy_key set=%s index=%s type=%s fingerprint=%s\n' \
      "$label" "$index" "$key_type" "$fingerprint"
    printf '%s\n' "$fingerprint" >>"$tmp/policy-$label-fingerprints"
    index=$((index + 1))
  done < <(jq -er --arg field "$field" '.[$field][]' "$policy_file")
}

printf '%s\n' '== Access policy shape and key fingerprints =='
access_secret "$access_policy" "$tmp/access-policy.json"
jq -er '
  type == "object"
  and ((keys | sort) == ([
    "deploy_mode",
    "deployer_ssh_public_keys",
    "join_mode",
    "member_ssh_public_keys",
    "version"
  ] | sort))
  and .version == 1
  and (.join_mode == "allowlist" or .join_mode == "open")
  and (.deploy_mode == "allowlist" or .deploy_mode == "all-users")
  and (.member_ssh_public_keys | type == "array")
  and (.deployer_ssh_public_keys | type == "array")
  and all(.member_ssh_public_keys[]; type == "string" and length > 0)
  and all(.deployer_ssh_public_keys[]; type == "string" and length > 0)
' "$tmp/access-policy.json" >/dev/null || {
  echo "latest access policy has an invalid shape" >&2
  exit 1
}
printf 'access_policy version=%s join_mode=%s deploy_mode=%s\n' \
  "$(jq -er .version "$tmp/access-policy.json")" \
  "$(jq -er .join_mode "$tmp/access-policy.json")" \
  "$(jq -er .deploy_mode "$tmp/access-policy.json")"
inspect_policy_keys member_ssh_public_keys member "$tmp/access-policy.json"
inspect_policy_keys deployer_ssh_public_keys deployer "$tmp/access-policy.json"
member_duplicates=0
deployer_duplicates=0
membership_overlap=0
if [[ -f "$tmp/policy-member-fingerprints" ]]; then
  member_duplicates="$(
    sort "$tmp/policy-member-fingerprints" | uniq -d | sed '/^$/d' | wc -l
  )"
fi
if [[ -f "$tmp/policy-deployer-fingerprints" ]]; then
  deployer_duplicates="$(
    sort "$tmp/policy-deployer-fingerprints" | uniq -d | sed '/^$/d' | wc -l
  )"
fi
if [[ -f "$tmp/policy-member-fingerprints" &&
  -f "$tmp/policy-deployer-fingerprints" ]]; then
  membership_overlap="$(
    comm -12 \
      <(sort -u "$tmp/policy-member-fingerprints") \
      <(sort -u "$tmp/policy-deployer-fingerprints") |
      sed '/^$/d' |
      wc -l
  )"
fi
printf 'access_policy_relationships member_duplicates=%s deployer_duplicates=%s member_deployer_overlap=%s\n' \
  "$member_duplicates" "$deployer_duplicates" "$membership_overlap"

inspect_kms_key() {
  local key="$1" keyring="${prefix}-snapshots"
  local description="$tmp/kms-$key.json" versions="$tmp/kms-$key-versions.json"
  gcloud kms keys describe "$key" \
    --keyring="$keyring" \
    --location="$region" \
    --project="$project" \
    --format=json >"$description"
  gcloud kms keys versions list \
    --key="$key" \
    --keyring="$keyring" \
    --location="$region" \
    --project="$project" \
    --format=json >"$versions"
  primary="$(jq -er '.primary.name | split("/")[-1]' "$description")"
  printf 'kms_key key=%s primary_version=%s purpose=%s rotation_period=%s\n' \
    "$key" \
    "$primary" \
    "$(jq -er '.purpose' "$description")" \
    "$(jq -r '.rotationPeriod // "manual"' "$description")"
  jq -er --arg key "$key" --arg primary "$primary" '
    .[]
    | [
        $key,
        (.name | split("/")[-1]),
        .state,
        (if (.name | split("/")[-1]) == $primary then "yes" else "no" end),
        (.createTime // "-"),
        (.destroyTime // "-")
      ]
    | @tsv
  ' "$versions" |
    while IFS=$'\t' read -r name version state is_primary created destroyed; do
      printf 'kms_version key=%s version=%s state=%s primary=%s created=%q destroyed=%q\n' \
        "$name" "$version" "$state" "$is_primary" "$created" "$destroyed"
    done
}

printf '%s\n' '== Snapshot KMS primary/enabled-version inventory =='
inspect_kms_key snapshot-envelope
inspect_kms_key snapshot-bucket

printf '%s\n' '== Terraform backend safety =='
"$ROOT/hack/inspect-terraform-backend.sh" \
  --terraform-dir "$terraform_dir" \
  --project "$project"

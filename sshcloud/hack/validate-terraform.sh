#!/usr/bin/env bash
# Format-check + terraform validate for sshcloud/terraform.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TF="$ROOT/terraform"

need=(
  versions.tf variables.tf outputs.tf main.tf services.tf iam.tf firestore.tf storage.tf kms.tf
  secrets.tf images.tf network.tf gateway.tf orchestrator.tf snapshotd.tf agents.tf demo.tf
  modules/project-services/main.tf
  scripts/gateway.sh.tftpl scripts/orchestrator.sh.tftpl scripts/snapshotd.sh.tftpl scripts/agent.sh.tftpl
  scripts/run-container.sh.tftpl scripts/ssh-client.sh scripts/deploy-fortune.sh
  scripts/verify-fortune.sh terraform.tfvars.example README.md
  ../hack/drain-agent-host.sh
  ../hack/preflight-gcp.sh
)
for f in "${need[@]}"; do
  if [[ ! -f "$TF/$f" ]]; then
    echo "missing $TF/$f" >&2
    exit 1
  fi
done

if ! grep -q 'ko-build/ko' "$TF/versions.tf"; then
  echo "versions.tf must require ko-build/ko" >&2
  exit 1
fi
if ! grep -q 'ko_build' "$TF/images.tf"; then
  echo "images.tf must declare ko_build resources" >&2
  exit 1
fi
if ! grep -q 'ko_build" "snapshot' "$TF/images.tf" ||
  ! grep -q 'RoleSnapshot' "$ROOT/internal/controlauth/auth.go" ||
  ! grep -q 'spiffe://sshcloud.internal/control/snapshot' "$TF/secrets.tf" ||
  ! grep -q 'google_compute_instance" "snapshot' "$TF/snapshotd.tf" ||
  ! grep -q 'agents_to_snapshot' "$TF/network.tf" ||
  ! grep -q -- '-snapshotd-url' "$TF/scripts/agent.sh.tftpl"; then
  echo "snapshotd needs a ko image, workload certificate, VM, private firewall, and agent RemoteStore URL" >&2
  exit 1
fi
if grep -q 'agent_snapshots' "$TF/iam.tf" ||
  grep -q 'serviceAccount:.*agent.email.*storage.object' "$TF/iam.tf" ||
  grep -q -- '-gcs-bucket' "$TF/scripts/agent.sh.tftpl"; then
  echo "the agent must have zero direct snapshot-bucket access" >&2
  exit 1
fi
if ! grep -q 'cloudkms.googleapis.com' "$TF/services.tf" ||
  ! grep -q 'google_kms_crypto_key" "snapshot_bucket' "$TF/kms.tf" ||
  ! grep -q 'google_kms_crypto_key" "snapshot_envelope' "$TF/kms.tf" ||
  ! grep -q 'default_kms_key_name' "$TF/storage.tf" ||
  ! grep -q 'snapshot_kek' "$TF/iam.tf" ||
  ! grep -q 'snapshot_bucket_cmek' "$TF/kms.tf"; then
  echo "snapshot envelope encryption and bucket CMEK resources are incomplete" >&2
  exit 1
fi
if ! grep -q 'enable_nested_virtualization' "$TF/agents.tf"; then
  echo "agents.tf must enable nested virtualization" >&2
  exit 1
fi
if ! grep -q 'google_storage_bucket_object" "jailer' "$TF/storage.tf" ||
  ! grep -q 'variable "jailer_asset_path"' "$TF/variables.tf" ||
  ! grep -q 'ko_build" "vmmhelper' "$TF/images.tf" ||
  ! grep -q 'ko_build" "taphelper' "$TF/images.tf"; then
  echo "Terraform must upload the jailer and build both isolation helpers" >&2
  exit 1
fi
agent_startup="$TF/scripts/agent.sh.tftpl"
if grep -Eq 'chmod[[:space:]]+0?666[[:space:]]+/dev/kvm' "$agent_startup"; then
  echo "production startup must never make /dev/kvm world-writable" >&2
  exit 1
fi
if [[ "$(grep -c '^SocketMode=0600$' "$agent_startup")" -ne 2 ]] ||
  ! grep -q 'Description=sshcloud root Firecracker jailer helper' "$agent_startup" ||
  ! grep -q 'Description=sshcloud CAP_NET_ADMIN-only TAP helper' "$agent_startup"; then
  echo "both host helpers need private systemd sockets and dedicated services" >&2
  exit 1
fi
agent_service="$(
  sed -n '/cat >\/etc\/systemd\/system\/sshcloud-agent.service <<EOF/,/^EOF$/p' "$agent_startup"
)"
if [[ "$agent_service" == *"CAP_NET_ADMIN"* ]] ||
  [[ "$agent_service" == *"SSHCLOUD_IP_DIRECT"* ]] ||
  [[ "$agent_service" == *"-direct-runtime"* ]] ||
  [[ "$agent_service" == *"-firecracker"* ]] ||
  [[ "$agent_service" == *"-kernel"* ]] ||
  [[ "$agent_service" != *"DevicePolicy=closed"* ]] ||
  ! grep -qx 'AmbientCapabilities=' <<<"$agent_service" ||
  ! grep -qx 'CapabilityBoundingSet=' <<<"$agent_service"; then
  echo "the production agent service must have empty capabilities and no direct VMM/network mode" >&2
  exit 1
fi
vmm_service="$(
  sed -n '/cat >\/etc\/systemd\/system\/sshcloud-vmmhelper.service <<EOF/,/^EOF$/p' "$agent_startup"
)"
if [[ "$vmm_service" == *"CAP_NET_ADMIN"* ]] ||
  [[ "$vmm_service" != *"User=root"* ]] ||
  [[ "$vmm_service" != *"-jailer /var/lib/sshcloud/assets/jailer"* ]] ||
  [[ "$vmm_service" != *"DeviceAllow=/dev/kvm rwm"* ]] ||
  [[ "$vmm_service" != *"Before=sshcloud-agent.service"* ]]; then
  echo "the root VMM helper must own the fixed jailer/KVM boundary without CAP_NET_ADMIN" >&2
  exit 1
fi
tap_service="$(
  sed -n '/cat >\/etc\/systemd\/system\/sshcloud-taphelper.service <<EOF/,/^EOF$/p' "$agent_startup"
)"
if [[ "$tap_service" != *"User=sshcloud-tap"* ]] ||
  [[ "$tap_service" != *"AmbientCapabilities=CAP_NET_ADMIN"* ]] ||
  [[ "$tap_service" != *"CapabilityBoundingSet=CAP_NET_ADMIN"* ]] ||
  [[ "$tap_service" != *"DeviceAllow=/dev/net/tun rw"* ]] ||
  [[ "$tap_service" != *"RestrictAddressFamilies=AF_UNIX AF_NETLINK AF_INET AF_INET6"* ]]; then
  echo "the TAP helper must run separately with only CAP_NET_ADMIN" >&2
  exit 1
fi
if ! grep -q 'google_firestore_database' "$TF/firestore.tf"; then
  echo "firestore.tf must declare google_firestore_database" >&2
  exit 1
fi
if ! grep -q 'module "project_services"' "$TF/services.tf"; then
  echo "services.tf must declare the API-enablement module" >&2
  exit 1
fi
if ! grep -q 'depends_on = \[module.project_services\]' "$TF/gateway.tf"; then
  echo "the Compute image lookup must wait for API enablement" >&2
  exit 1
fi
if ! grep -q 'triggers_replace' "$TF/demo.tf"; then
  echo "demo.tf must rerun bootstrap when its deployment inputs change" >&2
  exit 1
fi
if ! grep -q 'terraform_data" "smoke_test_fortune' "$TF/demo.tf"; then
  echo "demo.tf must verify fortune after deployment" >&2
  exit 1
fi
for variable in member_ssh_public_keys deployer_ssh_public_keys access_join_mode access_deploy_mode; do
  if ! grep -q "variable \"$variable\"" "$TF/variables.tf"; then
    echo "variables.tf must declare $variable" >&2
    exit 1
  fi
done
if [[ "$(grep -c 'default     = "allowlist"' "$TF/variables.tf")" -lt 2 ]]; then
  echo "join and deploy access modes must default to allowlist" >&2
  exit 1
fi
if ! grep -q 'google_secret_manager_secret_version" "access_policy' "$TF/secrets.tf" ||
  ! grep -q 'member_ssh_public_keys.*local.access_member_ssh_public_keys' "$TF/secrets.tf" ||
  ! grep -q 'deployer_ssh_public_keys.*local.access_deployer_ssh_public_keys' "$TF/secrets.tf" ||
  ! grep -q 'demo_ssh_public_keys' "$TF/secrets.tf" ||
  ! grep -q 'gateway_access_policy' "$TF/iam.tf"; then
  echo "Terraform must version, grant, and populate the access policy (including the opt-in demo key)" >&2
  exit 1
fi
if ! grep -q 'versions/latest:access' "$TF/scripts/gateway.sh.tftpl" ||
  ! grep -q 'sshcloud-access-policy-refresh.timer' "$TF/scripts/gateway.sh.tftpl" ||
  ! grep -q -- '-access-policy-file' "$TF/scripts/gateway.sh.tftpl"; then
  echo "gateway startup must refresh and enforce the latest access policy" >&2
  exit 1
fi
if ! grep -q 'google_secret_manager_secret_version.access_policy.id' "$TF/demo.tf"; then
  echo "demo bootstrap must rerun when the access policy changes" >&2
  exit 1
fi
if ! grep -q 'method="POST"' "$TF/scripts/orchestrator.sh.tftpl"; then
  echo "MIG listManagedInstances discovery must use POST" >&2
  exit 1
fi
bash -n "$TF/scripts/ssh-client.sh"
bash -n "$TF/scripts/deploy-fortune.sh"
bash -n "$TF/scripts/verify-fortune.sh"
bash -n "$ROOT/hack/drain-agent-host.sh"
bash -n "$ROOT/hack/preflight-gcp.sh"

smoke_bin="$(mktemp -d)"
trap 'rm -rf "$smoke_bin"' EXIT
cat >"$smoke_bin/ssh" <<'EOF'
#!/usr/bin/env bash
args=" $* "
for required in \
  " StrictHostKeyChecking=yes " \
  " IdentitiesOnly=yes " \
  " GlobalKnownHostsFile=/dev/null " \
  " fortune@192.0.2.1 "; do
  if [[ "$args" != *"$required"* ]]; then
    echo "missing strict SSH argument:$required" >&2
    exit 9
  fi
done
echo "hello demo"
EOF
chmod +x "$smoke_bin/ssh"
PATH="$smoke_bin:$PATH" \
  DEMO_KEY_PEM=test-private-key \
  HOST_PUB="ssh-ed25519 AAAA" \
  VERIFY_RETRIES=1 \
  "$TF/scripts/verify-fortune.sh" 192.0.2.1 fortune >/dev/null
rm -rf "$smoke_bin"
trap - EXIT

if command -v terraform >/dev/null 2>&1; then
  terraform -chdir="$TF" fmt -check -recursive
  terraform -chdir="$TF" init -backend=false -input=false >/tmp/sshcloud-tf-init.log
  terraform -chdir="$TF" validate
else
  echo "terraform CLI not installed; skipped fmt/validate (structure checks passed)"
fi

echo "terraform checks passed"

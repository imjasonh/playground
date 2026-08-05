#!/usr/bin/env bash
# Format-check + terraform validate for sshcloud/terraform.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TF="$ROOT/terraform"

need=(
  versions.tf variables.tf outputs.tf main.tf services.tf iam.tf firestore.tf storage.tf
  secrets.tf images.tf network.tf gateway.tf orchestrator.tf agents.tf demo.tf
  modules/project-services/main.tf
  scripts/gateway.sh.tftpl scripts/orchestrator.sh.tftpl scripts/agent.sh.tftpl
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
if ! grep -q 'enable_nested_virtualization' "$TF/agents.tf"; then
  echo "agents.tf must enable nested virtualization" >&2
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

#!/usr/bin/env bash
# Format-check + terraform validate for sshcloud/terraform.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TF="$ROOT/terraform"

need=(
  versions.tf variables.tf outputs.tf main.tf iam.tf firestore.tf storage.tf
  secrets.tf images.tf network.tf gateway.tf orchestrator.tf agents.tf demo.tf
  scripts/gateway.sh.tftpl scripts/orchestrator.sh.tftpl scripts/agent.sh.tftpl
  scripts/run-container.sh.tftpl scripts/deploy-fortune.sh terraform.tfvars.example README.md
  ../hack/drain-agent-host.sh
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
if ! grep -q 'triggers_replace' "$TF/demo.tf"; then
  echo "demo.tf must rerun bootstrap when its deployment inputs change" >&2
  exit 1
fi
if ! grep -q 'method="POST"' "$TF/scripts/orchestrator.sh.tftpl"; then
  echo "MIG listManagedInstances discovery must use POST" >&2
  exit 1
fi
bash -n "$TF/scripts/deploy-fortune.sh"
bash -n "$ROOT/hack/drain-agent-host.sh"

if command -v terraform >/dev/null 2>&1; then
  terraform -chdir="$TF" fmt -check -recursive
  terraform -chdir="$TF" init -backend=false -input=false >/tmp/sshcloud-tf-init.log
  terraform -chdir="$TF" validate
else
  echo "terraform CLI not installed; skipped fmt/validate (structure checks passed)"
fi

echo "terraform checks passed"

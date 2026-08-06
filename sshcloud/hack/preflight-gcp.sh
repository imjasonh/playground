#!/usr/bin/env bash
# Read-only checks before the first real sshcloud Terraform apply.
set -euo pipefail

PROJECT="${1:?usage: preflight-gcp.sh PROJECT [REGION] [ZONE]}"
REGION="${2:-us-central1}"
ZONE="${3:-${REGION}-a}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

for command in gcloud terraform go; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 1
  }
done

cli_account="$(gcloud config get-value account 2>/dev/null)"
echo "gcloud account: $cli_account"
if ! gcloud auth application-default print-access-token >/dev/null; then
  echo "Application Default Credentials are missing; run: gcloud auth application-default login" >&2
  exit 1
fi
echo "Application Default Credentials: available (principal not queried)"
gcloud projects describe "$PROJECT" --format='value(projectId)' >/dev/null

required_services=(
  compute.googleapis.com
  firestore.googleapis.com
  secretmanager.googleapis.com
  artifactregistry.googleapis.com
  iam.googleapis.com
  iamcredentials.googleapis.com
  storage.googleapis.com
  serviceusage.googleapis.com
  cloudresourcemanager.googleapis.com
  iap.googleapis.com
)
enabled="$(gcloud services list --enabled --project "$PROJECT" --format='value(config.name)' 2>/dev/null || true)"
for service in "${required_services[@]}"; do
  if ! grep -qx "$service" <<<"$enabled"; then
    echo "Terraform will enable API: $service"
  fi
done

for asset in firecracker jailer vmlinux; do
  path="$ROOT/_assets/$asset"
  [[ -s "$path" ]] || {
    echo "missing asset: $path (run hack/fetch-firecracker-assets.sh)" >&2
    exit 1
  }
done
if [[ "$(uname -s)" == "Linux" && "$(uname -m)" =~ ^(x86_64|amd64)$ ]]; then
  "$ROOT/_assets/firecracker" --version
  "$ROOT/_assets/jailer" --version
fi

terraform -chdir="$ROOT/terraform" init -backend=false -input=false >/dev/null
terraform -chdir="$ROOT/terraform" validate >/dev/null
go version

echo "preflight passed for project=$PROJECT region=$REGION zone=$ZONE"
echo "next: review terraform.tfvars, especially ssh_client_cidrs"

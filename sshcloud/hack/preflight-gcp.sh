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

echo "account: $(gcloud config get-value account 2>/dev/null)"
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
)
enabled="$(gcloud services list --enabled --project "$PROJECT" --format='value(config.name)')"
missing=0
for service in "${required_services[@]}"; do
  if ! grep -qx "$service" <<<"$enabled"; then
    echo "missing enabled API: $service" >&2
    missing=1
  fi
done
[[ "$missing" -eq 0 ]] || exit 1

if ! gcloud firestore databases describe --database='(default)' --project "$PROJECT" \
  --format='table(name,type,locationId)'; then
  if [[ "${MANAGE_FIRESTORE_DATABASE:-false}" != "true" ]]; then
    echo "a Native-mode (default) Firestore database is required; or set MANAGE_FIRESTORE_DATABASE=true and the Terraform variable" >&2
    exit 1
  fi
  echo "Firestore default database will be created by Terraform"
fi
gcloud compute machine-types describe n2-standard-4 --zone "$ZONE" --project "$PROJECT" \
  --format='value(name)' >/dev/null

for asset in firecracker vmlinux; do
  path="$ROOT/_assets/$asset"
  [[ -s "$path" ]] || {
    echo "missing asset: $path (run hack/fetch-firecracker-assets.sh)" >&2
    exit 1
  }
done
if [[ "$(uname -s)" == "Linux" && "$(uname -m)" =~ ^(x86_64|amd64)$ ]]; then
  "$ROOT/_assets/firecracker" --version
fi

terraform -chdir="$ROOT/terraform" init -backend=false -input=false >/dev/null
terraform -chdir="$ROOT/terraform" validate >/dev/null
go version

echo "preflight passed for project=$PROJECT region=$REGION zone=$ZONE"
echo "next: review terraform.tfvars, especially ssh_client_cidrs and manage_firestore_database"

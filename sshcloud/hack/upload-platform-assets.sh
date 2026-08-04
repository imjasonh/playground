#!/usr/bin/env bash
# Upload Firecracker binary and kernel to the Terraform assets bucket.
# Apps (including fortune) are digest-pinned OCI images — not uploaded here.
#
#   bash hack/fetch-firecracker-assets.sh
#   bash hack/upload-platform-assets.sh gs://sshcloud-PROJECT-assets
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUCKET="${1:?usage: upload-platform-assets.sh gs://bucket}"
ASSETS="${ASSETS:-$ROOT/_assets}"

for f in firecracker vmlinux; do
  if [[ ! -f "$ASSETS/$f" ]]; then
    echo "missing $ASSETS/$f" >&2
    exit 1
  fi
done

gsutil cp "$ASSETS/firecracker" "$ASSETS/vmlinux" "$BUCKET/"
echo "uploaded assets to $BUCKET"
echo "restart agent MIG VMs (or wait for next recreate) to pick them up:"
echo "  gcloud compute instance-groups managed rolling-action restart sshcloud-agents --zone=ZONE"
echo "deploy the sample app with:"
echo "  terraform -chdir=terraform output -raw fortune_image"

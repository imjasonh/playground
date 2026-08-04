#!/usr/bin/env bash
# Upload Firecracker binary, kernel, and fortune rootfs to the Terraform assets bucket.
#
#   bash hack/fetch-firecracker-assets.sh
#   go build -o _assets/fortune ./cmd/fortune
#   # CA pub from Secret Manager or local:
#   gcloud secrets versions access latest --secret=sshcloud-user-ca-pub > ssh_user_ca.pub
#   go run ./cmd/mkrootfs -fortune _assets/fortune -ca-pub ssh_user_ca.pub -out _assets/fortune-rootfs.ext4
#   bash hack/upload-platform-assets.sh gs://sshcloud-PROJECT-assets
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUCKET="${1:?usage: upload-platform-assets.sh gs://bucket}"
ASSETS="${ASSETS:-$ROOT/_assets}"

for f in firecracker vmlinux fortune-rootfs.ext4 fortune-rootfs.boot.json; do
  if [[ ! -f "$ASSETS/$f" ]]; then
    echo "missing $ASSETS/$f" >&2
    exit 1
  fi
done

gsutil cp "$ASSETS/firecracker" "$ASSETS/vmlinux" \
  "$ASSETS/fortune-rootfs.ext4" "$ASSETS/fortune-rootfs.boot.json" "$BUCKET/"
echo "uploaded assets to $BUCKET"
echo "restart agent MIG VMs (or wait for next recreate) to pick them up:"
echo "  gcloud compute instance-groups managed rolling-action restart sshcloud-agents --zone=ZONE"

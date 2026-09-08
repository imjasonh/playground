#!/usr/bin/env bash
# Run the image produced by build.sh. Needs a container runtime.
#
# If BUN_IMAGE_OUT is set, build.sh writes a tarball and this script loads it
# before docker run. Otherwise docker pulls the digest that build.sh pushed.
set -euo pipefail

cd "$(dirname "$0")"

ref="$(./build.sh "$@")"
if [[ -n "${BUN_IMAGE_OUT:-}" ]]; then
  docker load -i "$BUN_IMAGE_OUT"
fi
docker run --rm -p 8000:8000 "$ref"

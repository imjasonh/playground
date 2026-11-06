#!/usr/bin/env bash
# Builds the frontend with ko, builds an apko configuration with
# "docker buildx build", runs the image, and rebuilds with --no-cache to
# check that the image digest doesn't change.
#
# Usage: demo/run.sh [CONFIG]
#
# CONFIG defaults to demo/alpine.apko.yaml. Set REGISTRY to push somewhere
# other than a registry container on localhost:5000.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

config="${1:-demo/alpine.apko.yaml}"
registry="${REGISTRY:-localhost:5000}"
frontend="${registry}/apko-frontend"
image="${registry}/apko-frontend-demo:$(basename "${config}" .apko.yaml)"

if [[ "${registry}" == "localhost:5000" ]] && ! docker inspect registry >/dev/null 2>&1; then
  docker run -d --name registry -p 5000:5000 registry:2
fi

echo "Building the frontend with ko"
KO_DOCKER_REPO="${frontend}" ko build --bare \
  --platform=linux/amd64,linux/arm64 \
  --image-label moby.buildkit.frontend.network.none=true .

tmp="$(mktemp -d)"
trap 'rm -rf "${tmp}"' EXIT

# BUILDKIT_SYNTAX overrides the "# syntax=" line, so the demo files work
# with any REGISTRY. A provenance attestation records when the build ran,
# so the comparison leaves it out.
build() {
  local metadata="$1"
  shift
  docker buildx build \
    --build-arg "BUILDKIT_SYNTAX=${frontend}" \
    --provenance=false \
    --metadata-file "${metadata}" \
    --push -f "${config}" -t "${image}" "$@" "$(dirname "${config}")"
}

digest() {
  grep -o '"containerimage.digest": *"[^"]*"' "$1" | grep -o 'sha256:[0-9a-f]*'
}

echo "Building ${config}"
build "${tmp}/first.json"
docker run --rm "${image}"

echo "Rebuilding ${config} with --no-cache"
build "${tmp}/second.json" --no-cache

first="$(digest "${tmp}/first.json")"
second="$(digest "${tmp}/second.json")"
echo "first build:  ${first}"
echo "second build: ${second}"
if [[ "${first}" != "${second}" ]]; then
  echo "The rebuild produced a different image." >&2
  exit 1
fi
echo "Both builds produced the same image."

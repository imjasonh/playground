#!/usr/bin/env bash
# Build a multi-arch app image the way pack supports today:
#   1. pack build per --platform (linux/amd64, linux/arm64)
#   2. pack manifest create → OCI image index
#
# This mirrors `ko build --platform=linux/amd64,linux/arm64`. Go cross-compilation
# inside each platform's build container is handled by the buildpack via
# CNB_TARGET_ARCH (set by the lifecycle from the selected run image).
#
# Usage:
#   ./scripts/build-multiarch.sh <image> [pack build args...]
#
# Examples:
#   ./scripts/build-multiarch.sh myapp \
#     --builder ttl.sh/me-go-builder:1h \
#     --path testdata/hello \
#     --publish
#
#   PLATFORMS=linux/amd64 ./scripts/build-multiarch.sh myapp --builder go-builder:local --path .
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <image-name> [pack build flags...]" >&2
  exit 2
fi

image="$1"
shift

if ! command -v pack >/dev/null 2>&1; then
  echo "pack CLI not found — install from https://buildpacks.io/docs/tools/pack/" >&2
  exit 1
fi

PLATFORMS="${PLATFORMS:-linux/amd64,linux/arm64}"
publish=0
pack_args=()
for arg in "$@"; do
  if [[ "$arg" == "--publish" ]]; then
    publish=1
    continue
  fi
  pack_args+=("$arg")
done

IFS=',' read -r -a platforms <<<"$PLATFORMS"
manifest_refs=()

for platform in "${platforms[@]}"; do
  platform="$(echo "$platform" | tr -d '[:space:]')"
  [[ -n "$platform" ]] || continue
  arch="${platform##*/}"
  tag="${image}-${arch}"
  echo "→ pack build ${tag} --platform ${platform}"
  build_flags=(--platform "$platform")
  if ((publish)); then
    build_flags+=(--publish)
  fi
  pack build "$tag" "${build_flags[@]}" "${pack_args[@]}"
  manifest_refs+=("$tag")
done

echo "→ pack manifest create ${image} ${manifest_refs[*]}"
manifest_flags=(--format oci)
if ((publish)); then
  manifest_flags+=(--publish)
fi
pack manifest create "$image" "${manifest_refs[@]}" "${manifest_flags[@]}"

echo
echo "Multi-arch image: ${image}"
echo "Per-arch tags:    ${manifest_refs[*]}"
if ((publish)); then
  echo "Published to registry (OCI index)."
else
  echo "Index kept locally by pack; re-run with --publish to push."
fi

# Silence unused root in case we later need it for defaults.
: "$root"

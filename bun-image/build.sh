#!/usr/bin/env bash
# Build a container image from example.js using bun compile + crane.
# No Dockerfile and no docker build. A container runtime is only needed
# to run the image (see run.sh).
#
# Usage:
#   ./build.sh [image] [base]
#
# Environment:
#   BUN_IMAGE_OUT  Write a docker-save tarball here instead of pushing.
#   BUN_TARGET     bun --compile --target (default: host glibc Linux target).
set -euo pipefail

cd "$(dirname "$0")"

need() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "need $1 on PATH" >&2
    exit 1
  fi
}

need bun
need crane

image="${1:-gcr.io/imjasonh/bun}"
base="${2:-gcr.io/distroless/cc-debian12}"

host_arch="$(uname -m)"
case "$host_arch" in
  x86_64 | amd64) default_target="bun-linux-x64" ;;
  aarch64 | arm64) default_target="bun-linux-arm64" ;;
  *)
    echo "unsupported host architecture: ${host_arch}" >&2
    exit 1
    ;;
esac

target="${BUN_TARGET:-$default_target}"

case "$target" in
  *linux*x64*) platform="linux/amd64" ;;
  *linux*arm64*) platform="linux/arm64" ;;
  *)
    echo "BUN_TARGET must be a bun-linux-* target, got: ${target}" >&2
    exit 1
    ;;
esac

# bun-linux-*-musl is still dynamically linked to musl libc and libstdc++.
# distroless/cc is glibc; distroless/static has no libc. Neither will run it.
if [[ "$target" == *musl* ]]; then
  case "$base" in
    *distroless/cc* | *distroless/static*)
      echo "bun's musl compile target is dynamically linked; it will not run on ${base}" >&2
      echo "use an Alpine (or other musl + libstdc++) base, or omit BUN_TARGET for glibc + distroless/cc" >&2
      exit 1
      ;;
  esac
fi

bin="example"
rm -f "$bin"

echo "compiling example.js (${target})" >&2
bun build --compile --minify --target="$target" ./example.js --outfile="$bin" >&2

if [[ ! -x "$bin" ]]; then
  echo "bun compile did not write an executable ${bin}" >&2
  exit 1
fi

layer="$(mktemp)"
trap 'rm -f "$layer"' EXIT
tar -cf "$layer" "$bin"

if [[ -n "${BUN_IMAGE_OUT:-}" ]]; then
  echo "writing ${BUN_IMAGE_OUT} from ${base} (${platform})" >&2
  crane --platform "$platform" mutate "$base" \
    --append "$layer" \
    --entrypoint="/${bin}" \
    --exposed-ports=8000 \
    --tag "$image" \
    --output "$BUN_IMAGE_OUT" >&2
  echo "$image"
else
  echo "pushing ${image} from ${base} (${platform})" >&2
  crane --platform "$platform" mutate "$base" \
    --append "$layer" \
    --entrypoint="/${bin}" \
    --exposed-ports=8000 \
    --tag "$image"
fi

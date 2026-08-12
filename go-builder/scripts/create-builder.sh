#!/usr/bin/env bash
# Package the buildpack and create a builder image.
#
# Default: multi-arch (linux/amd64 + linux/arm64), matching builder.toml targets.
# Multi-arch indexes must be published to a registry (Docker daemon cannot hold
# a real OCI index the way a registry can):
#
#   BUILDER_IMAGE=ttl.sh/my-go-builder:1h ./scripts/create-builder.sh
#
# Local single-arch (host) daemon builder:
#
#   ./scripts/create-builder.sh --local
#
# Requires: pack CLI, Docker (or compatible).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

BUILDER_IMAGE="${BUILDER_IMAGE:-go-builder:local}"
TARGETS="${TARGETS:-linux/amd64,linux/arm64}"
local_only=0
publish_args=()

usage() {
  cat <<EOF
Usage: $(basename "$0") [--local] [--publish]

  --local     Create a host-arch builder in the Docker daemon (no registry).
  --publish   Publish to BUILDER_IMAGE (default for multi-arch). Implied when
              BUILDER_IMAGE looks like a registry repo and --local is not set.

Env:
  BUILDER_IMAGE   Image ref (default: go-builder:local)
  TARGETS         Comma-separated pack targets (default: linux/amd64,linux/arm64)
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --local) local_only=1; shift ;;
    --publish) publish_args=(--publish); shift ;;
    -h | --help) usage; exit 0 ;;
    *) echo "unknown flag: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if ! command -v pack >/dev/null 2>&1; then
  echo "pack CLI not found — install from https://buildpacks.io/docs/tools/pack/" >&2
  exit 1
fi

target_flags=()
if ((local_only)); then
  bash scripts/package.sh --host
  host_arch="$(go env GOARCH)"
  target_flags+=(--target "linux/${host_arch}")
  echo "→ creating local single-arch builder (linux/${host_arch})"
else
  bash scripts/package.sh
  IFS=',' read -r -a target_list <<<"$TARGETS"
  for t in "${target_list[@]}"; do
    t="$(echo "$t" | tr -d '[:space:]')"
    [[ -n "$t" ]] || continue
    target_flags+=(--target "$t")
  done
  if ((${#publish_args[@]} == 0)); then
    # Multi-arch requires a registry; default to --publish.
    publish_args=(--publish)
  fi
  if [[ "$BUILDER_IMAGE" == go-builder:local ]]; then
    echo "BUILDER_IMAGE is 'go-builder:local' but multi-arch publish needs a registry ref." >&2
    echo "Example: BUILDER_IMAGE=ttl.sh/\$(whoami)-go-builder:1h $0" >&2
    echo "Or use:  $0 --local" >&2
    exit 1
  fi
  echo "→ creating multi-arch builder ${BUILDER_IMAGE} (${TARGETS})"
fi

pack builder create "${BUILDER_IMAGE}" \
  --config "${root}/builder.toml" \
  --pull-policy if-not-present \
  "${target_flags[@]}" \
  "${publish_args[@]}"

cat <<EOF

Builder ready: ${BUILDER_IMAGE}

Single-arch app:
  pack build hello-go --builder ${BUILDER_IMAGE} --path testdata/hello

Multi-arch app (amd64+arm64 index), same spirit as ko --platform=all:
  ./scripts/build-multiarch.sh hello-go --builder ${BUILDER_IMAGE} --path testdata/hello --publish
EOF

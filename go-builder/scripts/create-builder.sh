#!/usr/bin/env bash
# Package the buildpack and create a local builder image.
# Requires: pack CLI, Docker (or a compatible daemon).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

BUILDER_IMAGE="${BUILDER_IMAGE:-go-builder:local}"

if ! command -v pack >/dev/null 2>&1; then
  echo "pack CLI not found — install from https://buildpacks.io/docs/tools/pack/" >&2
  exit 1
fi

bash scripts/package.sh

echo "→ pack builder create ${BUILDER_IMAGE}"
pack builder create "${BUILDER_IMAGE}" --config "${root}/builder.toml" --pull-policy if-not-present

cat <<EOF

Builder ready: ${BUILDER_IMAGE}

Try it:

  pack build hello-go \\
    --builder ${BUILDER_IMAGE} \\
    --path testdata/hello \\
    --pull-policy if-not-present

  docker run --rm hello-go
EOF

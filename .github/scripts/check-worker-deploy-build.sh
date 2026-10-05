#!/usr/bin/env bash
# Build a Cloudflare Worker app the way deploy-workers.yml does, without
# uploading it. Run it from the app directory.
#
# wrangler-action installs Wrangler into the app directory before it deploys,
# which leaves a package.json there. A nested `dependencies` object in that
# file has broken worker-build before, so write the same decoy. Then
# `wrangler deploy --dry-run`, with the Wrangler version pinned in
# .github/wrangler/package.json, runs the [build] command, validates
# wrangler.toml and its bindings, and bundles the Worker.
#
# Wrangler only warns about wrangler.toml keys it doesn't recognize, and a
# deploy with that version drops those settings. Fail on that warning.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
version=$(jq -r '.devDependencies.wrangler' "$repo_root/.github/wrangler/package.json")

scratch=$(mktemp -d)
trap 'rm -rf package.json package-lock.json "$scratch"' EXIT
printf '{"dependencies":{"wrangler":"%s"}}\n' "$version" > package.json

npx -y "wrangler@${version}" deploy --dry-run --outdir "$scratch/dist" 2>&1 | tee "$scratch/wrangler.log"
if grep -q "Unexpected fields" "$scratch/wrangler.log"; then
  echo "::error title=wrangler.toml setting ignored::$(basename "$PWD"): Wrangler ${version} does not recognize part of wrangler.toml (see \"Unexpected fields\")."
  exit 1
fi
test -f build/worker/shim.mjs

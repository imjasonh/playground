#!/usr/bin/env bash
# Ensure a GHCR container package is public so exe.dev can pull without registry_auth.
#
# GITHUB_TOKEN can push packages (packages:write) but often cannot change visibility
# via PUT (.../visibility → 404). Prefer a GET: if the package is already public,
# succeed. Only attempt PUT when it is still private.
#
# Environment:
#   GHCR_PACKAGE  Package name under the current user/org (e.g. playground/chessh)
#   GITHUB_TOKEN  Token with packages:write
#   GITHUB_REPOSITORY_OWNER
set -euo pipefail

: "${GHCR_PACKAGE:?GHCR_PACKAGE must be set}"
: "${GITHUB_TOKEN:?GITHUB_TOKEN must be set}"
: "${GITHUB_REPOSITORY_OWNER:?GITHUB_REPOSITORY_OWNER must be set}"

encoded=$(python3 -c 'import urllib.parse,sys; print(urllib.parse.quote(sys.argv[1], safe=""))' "$GHCR_PACKAGE")

api_get() {
  local path="$1"
  curl -sS -o /tmp/ghcr-package.json -w '%{http_code}' \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/${path}"
}

api_put_public() {
  local path="$1"
  curl -sS -o /tmp/ghcr-visibility.json -w '%{http_code}' \
    -X PUT \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/${path}" \
    -d '{"visibility":"public"}'
}

package_paths=(
  "user/packages/container/${encoded}"
  "orgs/${GITHUB_REPOSITORY_OWNER}/packages/container/${encoded}"
)

found_path=""
for base in "${package_paths[@]}"; do
  code=$(api_get "$base")
  if [ "$code" = "200" ]; then
    found_path="$base"
    break
  fi
  echo "GET /${base} -> HTTP ${code}"
done

if [ -z "$found_path" ]; then
  echo "Could not find GHCR package ${GHCR_PACKAGE}." >&2
  cat /tmp/ghcr-package.json >&2 || true
  exit 1
fi

visibility=$(python3 - <<'PY'
import json
data = json.load(open("/tmp/ghcr-package.json"))
print(data.get("visibility") or "", end="")
PY
)

if [ "$visibility" = "public" ]; then
  echo "GHCR package ${GHCR_PACKAGE} is already public (${found_path})."
  exit 0
fi

echo "GHCR package ${GHCR_PACKAGE} visibility=${visibility}; attempting to set public."
put_code=$(api_put_public "${found_path}/visibility")
echo "PUT /${found_path}/visibility -> HTTP ${put_code}"
cat /tmp/ghcr-visibility.json || true
echo

# Re-check: GITHUB_TOKEN often cannot change visibility (PUT 404); a human may
# have flipped it in the UI, or a PAT with admin rights may have.
code=$(api_get "$found_path")
if [ "$code" = "200" ]; then
  visibility=$(python3 - <<'PY'
import json
data = json.load(open("/tmp/ghcr-package.json"))
print(data.get("visibility") or "", end="")
PY
  )
  if [ "$visibility" = "public" ]; then
    echo "GHCR package ${GHCR_PACKAGE} is public."
    exit 0
  fi
fi

echo "Could not set GHCR package ${GHCR_PACKAGE} to public." >&2
echo "GITHUB_TOKEN often cannot change package visibility. Make it public once in" >&2
echo "  https://github.com/users/${GITHUB_REPOSITORY_OWNER}/packages/container/package/${GHCR_PACKAGE}" >&2
echo "then re-run this workflow." >&2
exit 1

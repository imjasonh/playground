#!/usr/bin/env bash
# Make a GHCR container package public so exe.dev can pull without registry_auth.
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

# User-owned packages use /user/packages; org-owned use /orgs/{org}/packages.
# Try user first, then org.
for path in \
  "user/packages/container/${encoded}/visibility" \
  "orgs/${GITHUB_REPOSITORY_OWNER}/packages/container/${encoded}/visibility"
do
  code=$(curl -sS -o /tmp/ghcr-visibility.json -w '%{http_code}' \
    -X PUT \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/${path}" \
    -d '{"visibility":"public"}')
  if [ "$code" = "204" ] || [ "$code" = "200" ]; then
    echo "GHCR package ${GHCR_PACKAGE} is public (${path})."
    exit 0
  fi
  echo "PUT /${path} -> HTTP ${code}"
  cat /tmp/ghcr-visibility.json || true
  echo
done

echo "Could not set GHCR package ${GHCR_PACKAGE} to public." >&2
exit 1

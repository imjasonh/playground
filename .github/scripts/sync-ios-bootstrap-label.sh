#!/usr/bin/env bash
# Sync the needs-ios-bootstrap label on a pull request from a true/false flag.
#
# Usage:
#   sync-ios-bootstrap-label.sh <pr-number> <true|false>
#
# Creates the label if missing. Adds it when needed=true; removes it when
# needed=false and it is currently present.
set -euo pipefail

pr="${1:?Usage: $0 <pr-number> <true|false>}"
needed="${2:?Usage: $0 <pr-number> <true|false>}"
label="needs-ios-bootstrap"

: "${GH_TOKEN:?GH_TOKEN (or gh auth) is required}"
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must be set (owner/repo)}"

case "$needed" in
  true|false) ;;
  *)
    echo "needed must be true or false, got: $needed" >&2
    exit 1
    ;;
esac

# Ensure the label exists (color: amber — "action needed before ship").
if ! gh label list --repo "$GITHUB_REPOSITORY" --limit 1000 --json name \
  --jq '.[].name' | grep -Fxq "$label"; then
  gh label create "$label" \
    --repo "$GITHUB_REPOSITORY" \
    --description "iOS change needs signing re-bootstrap before TestFlight" \
    --color "D93F0B" \
    || true
fi

has_label=$(
  gh pr view "$pr" --repo "$GITHUB_REPOSITORY" --json labels \
    --jq "[.labels[].name] | index(\"${label}\") != null"
)

if [ "$needed" = "true" ]; then
  if [ "$has_label" = "true" ]; then
    echo "PR #${pr} already has ${label}"
  else
    gh pr edit "$pr" --repo "$GITHUB_REPOSITORY" --add-label "$label"
    echo "Labeled PR #${pr} with ${label}"
  fi
else
  if [ "$has_label" = "true" ]; then
    gh pr edit "$pr" --repo "$GITHUB_REPOSITORY" --remove-label "$label"
    echo "Removed ${label} from PR #${pr}"
  else
    echo "PR #${pr} does not have ${label} (nothing to do)"
  fi
fi

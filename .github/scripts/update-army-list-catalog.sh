#!/usr/bin/env bash
# Refresh the bundled Army List construction catalog and regenerate stress
# fixtures via the Swift ArmyListValidator (macOS). Used by the weekly workflow.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

RESULT=success
HAS_CHANGES=false
CATALOG="ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"

if [[ "$(uname -s)" != "Darwin" ]]; then
  echo "::error::Army list catalog update must run on macOS so stress fixtures use the Swift validator"
  RESULT=failure
fi

if [[ "$RESULT" == "success" ]]; then
  if ! python3 -c 'import yaml' >/dev/null 2>&1; then
    python3 -m pip install --user pyyaml -q
  fi
  if ! python3 ios/scripts/refresh-army-list-catalog.py; then
    RESULT=failure
  fi
fi

CATALOG_CHANGED=false
if [[ "$RESULT" == "success" ]]; then
  if ! git diff --quiet -- "$CATALOG"; then
    CATALOG_CHANGED=true
  fi
  # Always run the Swift harness so builder/validator stay in lockstep.
  # Only rewrite fixtures when the catalog itself changed; otherwise random
  # churn (or even deterministic rewrites of unchanged lists) opens empty PRs.
  if [[ "$CATALOG_CHANGED" == true ]]; then
    if ! bash ios/scripts/stress-army-lists.sh --write-fixtures; then
      RESULT=failure
    fi
  else
    if ! bash ios/scripts/stress-army-lists.sh; then
      RESULT=failure
    fi
  fi
fi

if [[ "$RESULT" == "success" ]]; then
  if ! git diff --quiet -- \
      "$CATALOG" \
      ios/Tests/PlaygroundTests/Fixtures/ArmyLists; then
    HAS_CHANGES=true
  fi
  if git ls-files --others --exclude-standard -- \
      "$CATALOG" \
      ios/Tests/PlaygroundTests/Fixtures/ArmyLists | grep -q .; then
    HAS_CHANGES=true
  fi
fi

{
  echo "result=${RESULT}"
  echo "has_changes=${HAS_CHANGES}"
} | {
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    cat >> "$GITHUB_OUTPUT"
  else
    cat >/dev/null
  fi
}

echo "Army list catalog update result=${RESULT} has_changes=${HAS_CHANGES} catalog_changed=${CATALOG_CHANGED:-false}"
if [[ "$RESULT" != "success" ]]; then
  exit 1
fi

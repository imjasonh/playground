#!/usr/bin/env bash
# Refresh the bundled Army List construction catalog and regenerate stress
# fixtures. Used by the weekly army-list-catalog workflow.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

RESULT=success
HAS_CHANGES=false

if ! python3 -c 'import yaml' >/dev/null 2>&1; then
  python3 -m pip install --user pyyaml -q
fi

if ! python3 ios/scripts/refresh-army-list-catalog.py; then
  RESULT=failure
fi

if [[ "$RESULT" == "success" ]]; then
  if ! python3 ios/scripts/stress-army-lists.py --write-fixtures; then
    RESULT=failure
  fi
fi

if [[ "$RESULT" == "success" ]]; then
  if ! git diff --quiet -- \
      ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json \
      ios/Tests/PlaygroundTests/Fixtures/ArmyLists \
      ios/scripts/refresh-army-list-catalog.py \
      ios/scripts/stress-army-lists.py; then
    HAS_CHANGES=true
  fi
  # Untracked fixture files also count as changes.
  if git ls-files --others --exclude-standard -- \
      ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json \
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

echo "Army list catalog update result=${RESULT} has_changes=${HAS_CHANGES}"
if [[ "$RESULT" != "success" ]]; then
  exit 1
fi

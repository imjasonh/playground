#!/usr/bin/env bash
# Refresh the bundled Army List construction catalog and regenerate stress
# fixtures via the Swift ArmyListValidator (macOS). Used by the weekly workflow.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

RESULT=success
HAS_CHANGES=false

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

if [[ "$RESULT" == "success" ]]; then
  if ! bash ios/scripts/stress-army-lists.sh --write-fixtures; then
    RESULT=failure
  fi
fi

if [[ "$RESULT" == "success" ]]; then
  if ! git diff --quiet -- \
      ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json \
      ios/Tests/PlaygroundTests/Fixtures/ArmyLists \
      ios/scripts/refresh-army-list-catalog.py \
      ios/scripts/stress-army-lists.sh \
      ios/Sources/Experiments/ArmyList/Stress \
      ios/Tools/ArmyListStress; then
    HAS_CHANGES=true
  fi
  if git ls-files --others --exclude-standard -- \
      ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json \
      ios/Tests/PlaygroundTests/Fixtures/ArmyLists \
      ios/Sources/Experiments/ArmyList/Stress \
      ios/Tools/ArmyListStress | grep -q .; then
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

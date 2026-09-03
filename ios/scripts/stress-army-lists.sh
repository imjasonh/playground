#!/usr/bin/env bash
# Build ~50 army lists and validate them with the Swift ArmyListValidator.
# Optionally rewrite XCTest fixtures. Requires macOS + Xcode + XcodeGen.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
IOS_ROOT="$ROOT/ios"
DERIVED="${ARMY_LIST_STRESS_DERIVED:-/tmp/army-list-stress-derived}"
WRITE_FIXTURES=false

for arg in "$@"; do
  case "$arg" in
    --write-fixtures) WRITE_FIXTURES=true ;;
    --help|-h)
      echo "Usage: $0 [--write-fixtures]"
      echo "Requires macOS + Xcode. Validates with the Swift ArmyListValidator only."
      exit 0
      ;;
    *)
      echo "Unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

if [[ "$(uname -s)" != "Darwin" ]]; then
  echo "army-list-stress requires macOS + Xcode (Swift ArmyListValidator is canonical)." >&2
  exit 1
fi

cd "$IOS_ROOT"
if ! command -v xcodegen >/dev/null 2>&1; then
  echo "xcodegen is required; install with: brew install xcodegen" >&2
  exit 1
fi
xcodegen generate

rm -rf "$DERIVED"
xcodebuild \
  -project Playground.xcodeproj \
  -scheme ArmyListStress \
  -destination 'platform=macOS' \
  -derivedDataPath "$DERIVED" \
  -configuration Debug \
  build \
  CODE_SIGNING_ALLOWED=NO

BIN=$(find "$DERIVED/Build/Products" -type f -name ArmyListStress -perm -111 | head -n 1)
if [[ -z "$BIN" ]]; then
  echo "ArmyListStress binary not found under $DERIVED" >&2
  exit 1
fi

CATALOG="$IOS_ROOT/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"
FIXTURES="$IOS_ROOT/Tests/PlaygroundTests/Fixtures/ArmyLists"

ARGS=(--catalog "$CATALOG" --fixtures-dir "$FIXTURES")
if [[ "$WRITE_FIXTURES" == true ]]; then
  ARGS+=(--write-fixtures)
fi

"$BIN" "${ARGS[@]}"

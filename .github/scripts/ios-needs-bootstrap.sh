#!/usr/bin/env bash
# Decide whether an ios/ change needs Apple signing re-bootstrap.
#
# Prints "true" or "false" to stdout.
#
# Yes when the range touches:
#   - ios/fastlane/Matchfile
#   - ios/**/*.entitlements (host or extension App ID capabilities)
#   - ios/project.yml hunks for entitlements, CODE_SIGN_ENTITLEMENTS,
#     type: app-extension, or com.apple.developer.*
#   - ios/fastlane/Fastfile hunks that wire Bundle IDs / capabilities
#
# No for in-app experiments alone, and no for a macOS *tool* target inside
# ios/project.yml (e.g. ArmyListStress PRODUCT_BUNDLE_IDENTIFIER).
#
# Usage:
#   bash .github/scripts/ios-needs-bootstrap.sh <git-range>
# Example:
#   bash .github/scripts/ios-needs-bootstrap.sh origin/main...HEAD
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <git-range>" >&2
  exit 2
fi

range=$1
needed=false

while IFS= read -r path; do
  case "$path" in
    ios/fastlane/Matchfile|ios/*.entitlements|ios/*/*.entitlements)
      needed=true
      break
      ;;
    ios/project.yml)
      # Entitlements / extensions / App ID capabilities — not a lone
      # PRODUCT_BUNDLE_IDENTIFIER (macOS CLI tools under ios/ use that too).
      if git diff -U0 "$range" -- "$path" | grep -E '^[+-]' | grep -Ev '^[+-]{3} ' \
        | grep -Eq 'CODE_SIGN_ENTITLEMENTS|[[:space:]]entitlements:|type:[[:space:]]*app-extension|com\.apple\.developer\.'; then
        needed=true
        break
      fi
      ;;
    ios/fastlane/Fastfile)
      if git diff -U0 "$range" -- "$path" | grep -E '^[+-]' | grep -Ev '^[+-]{3} ' \
        | grep -Eq 'SIGNING_IDENTIFIERS|ensure_bundle_ids!|ensure_healthkit!|ensure_nfc_tag_reading!|APP_IDENTIFIER|KEYBOARD_IDENTIFIER|RIDE_WIDGET_IDENTIFIER|WATCH_IDENTIFIER|app_identifier:|BundleId|signing_bootstrap'; then
        needed=true
        break
      fi
      ;;
  esac
done < <(git diff --name-only "$range")

printf '%s\n' "$needed"

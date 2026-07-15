#!/usr/bin/env bash
# Tests for discover-ios-apps.sh and discover-macos-apps.sh.
# Run: bash .github/scripts/discover-xcodegen-apps_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
discover_ios="$script_dir/discover-ios-apps.sh"
discover_macos="$script_dir/discover-macos-apps.sh"

failures=0
assert_eq() {
  local got="$1" want="$2" label="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label" >&2
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
    failures=$((failures + 1))
  fi
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Fake repo root with one iOS app, one macOS app, and a decoy project.yml that
# is neither (e.g. a docs stub). Discovery must walk $PWD, so we cd into work.
mkdir -p "$work/ios" "$work/hello-macos" "$work/neither" "$work/.hidden"

cat > "$work/ios/project.yml" <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    platform: iOS
EOF

cat > "$work/hello-macos/project.yml" <<'EOF'
name: HelloMac
targets:
  HelloMac:
    type: application
    platform: macOS
EOF

cat > "$work/neither/project.yml" <<'EOF'
name: DocsOnly
# no platform: line
EOF

cat > "$work/.hidden/project.yml" <<'EOF'
name: Hidden
targets:
  Hidden:
    platform: macOS
EOF

(
  cd "$work"
  assert_eq "$(bash "$discover_ios" --all)" '["ios"]' "ios --all"
  assert_eq "$(bash "$discover_macos" --all)" '["hello-macos"]' "macos --all"

  assert_eq \
    "$(printf '%s\n' 'ios/Sources/App.swift' 'README.md' | bash "$discover_ios" --from-changes)" \
    '["ios"]' \
    "ios from-changes"

  assert_eq \
    "$(printf '%s\n' 'hello-macos/Sources/App.swift' 'ios/project.yml' | bash "$discover_macos" --from-changes)" \
    '["hello-macos"]' \
    "macos from-changes ignores ios path"

  assert_eq \
    "$(printf '%s\n' 'neither/project.yml' '.hidden/project.yml' | bash "$discover_macos" --from-changes)" \
    '[]' \
    "macos ignores non-macOS and hidden"
)

# Live repo sanity: ios/ must still count as iOS; hello-macos as macOS when present.
(
  cd "$repo_root"
  live_ios="$(bash "$discover_ios" --all)"
  if [[ "$live_ios" != *'"ios"'* ]]; then
    echo "FAIL: live repo ios discovery missing ios: $live_ios" >&2
    failures=$((failures + 1))
  fi
  if [[ -f hello-macos/project.yml ]]; then
    live_macos="$(bash "$discover_macos" --all)"
    if [[ "$live_macos" != *'"hello-macos"'* ]]; then
      echo "FAIL: live repo macos discovery missing hello-macos: $live_macos" >&2
      failures=$((failures + 1))
    fi
    # Cross-talk: ios discovery must not pick up hello-macos.
    if [[ "$live_ios" == *hello-macos* ]]; then
      echo "FAIL: ios discovery incorrectly includes hello-macos: $live_ios" >&2
      failures=$((failures + 1))
    fi
  fi
)

if ((failures > 0)); then
  echo "$failures test(s) failed." >&2
  exit 1
fi
echo "All discover-xcodegen-apps tests passed."

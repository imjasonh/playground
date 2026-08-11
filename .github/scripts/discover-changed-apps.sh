#!/usr/bin/env bash
# Discover changed testable browser apps, Go modules, Rust apps, iOS apps,
# macOS apps, and inkbot-esp32 firmware for the test / platform workflows.
set -euo pipefail

: "${EVENT_NAME:?EVENT_NAME must be set}"
: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# inkbot-esp32 is excluded from discover-rust-apps.sh (needs espup). Emit a
# JSON array so inkbot-esp32.yml can gate host/firmware jobs like ios/macos.
inkbot_esp32_from_changes() {
  local path
  while IFS= read -r path; do
    case "$path" in
      inkbot-esp32/* | .github/workflows/inkbot-esp32.yml)
        echo '["inkbot-esp32"]'
        return 0
        ;;
    esac
  done <<EOF
$1
EOF
  echo '[]'
}

if [ "$EVENT_NAME" = "pull_request" ]; then
  : "${BASE_REF:?BASE_REF must be set for pull requests}"
  git fetch origin "$BASE_REF"
  changed=$(git diff --name-only "origin/${BASE_REF}...HEAD")
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  if [ "$BEFORE_SHA" = "0000000000000000000000000000000000000000" ]; then
    echo "No prior commit; testing all apps."
    apps=$(bash .github/scripts/discover-testable-apps.sh --all)
    modules=$(bash .github/scripts/discover-go-modules.sh --all)
    rust=$(bash .github/scripts/discover-rust-apps.sh --all)
    ios=$(bash .github/scripts/discover-ios-apps.sh --all)
    macos=$(bash .github/scripts/discover-macos-apps.sh --all)
    inkbot_esp32='["inkbot-esp32"]'
    {
      echo "apps=${apps}"
      echo "modules=${modules}"
      echo "rust=${rust}"
      echo "ios=${ios}"
      echo "macos=${macos}"
      echo "inkbot_esp32=${inkbot_esp32}"
    } >> "$GITHUB_OUTPUT"
    echo "Testable browser apps: ${apps}"
    echo "Go apps: ${modules}"
    echo "Rust apps: ${rust}"
    echo "iOS apps: ${ios}"
    echo "macOS apps: ${macos}"
    echo "inkbot-esp32: ${inkbot_esp32}"
    exit 0
  else
    changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  fi
fi

if [ -z "$changed" ]; then
  apps='[]'
  modules='[]'
  rust='[]'
  ios='[]'
  macos='[]'
  inkbot_esp32='[]'
else
  apps=$(printf '%s\n' "$changed" | bash .github/scripts/discover-testable-apps.sh --from-changes)
  modules=$(printf '%s\n' "$changed" | bash .github/scripts/discover-go-modules.sh --from-changes)
  rust=$(printf '%s\n' "$changed" | bash .github/scripts/discover-rust-apps.sh --from-changes)
  ios=$(printf '%s\n' "$changed" | bash .github/scripts/discover-ios-apps.sh --from-changes)
  macos=$(printf '%s\n' "$changed" | bash .github/scripts/discover-macos-apps.sh --from-changes)
  inkbot_esp32=$(inkbot_esp32_from_changes "$changed")
fi

{
  echo "apps=${apps}"
  echo "modules=${modules}"
  echo "rust=${rust}"
  echo "ios=${ios}"
  echo "macos=${macos}"
  echo "inkbot_esp32=${inkbot_esp32}"
} >> "$GITHUB_OUTPUT"

echo "Changed paths:"
printf '%s\n' "$changed"
echo "Testable browser apps: ${apps}"
echo "Go apps: ${modules}"
echo "Rust apps: ${rust}"
echo "iOS apps: ${ios}"
echo "macOS apps: ${macos}"
echo "inkbot-esp32: ${inkbot_esp32}"

#!/usr/bin/env bash
# Discover changed testable browser apps, Go modules, Rust apps, iOS apps,
# macOS apps, ESP32 firmware crates, whether the pasta style leg should run,
# whether the posts catalog builder should run, whether the Pages home-page
# index renderer should run, and whether nescript.yml should run its ROM,
# jsnes, and Mesen checks.
set -euo pipefail

: "${EVENT_NAME:?EVENT_NAME must be set}"
: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

pasta_from_changes() {
  # discover-pasta.sh prints `pasta=true|false`; strip the key.
  printf '%s\n' "$1" | bash .github/scripts/discover-pasta.sh --from-changes | sed -n 's/^pasta=//p'
}

blog_from_changes() {
  # discover-blog.sh prints `blog=true|false`; strip the key.
  printf '%s\n' "$1" | bash .github/scripts/discover-blog.sh --from-changes | sed -n 's/^blog=//p'
}

index_from_changes() {
  # discover-index.sh prints `index=true|false`; strip the key.
  printf '%s\n' "$1" | bash .github/scripts/discover-index.sh --from-changes | sed -n 's/^index=//p'
}

nescript_from_changes() {
  # discover-nescript.sh prints `nescript=true|false`; strip the key.
  printf '%s\n' "$1" | bash .github/scripts/discover-nescript.sh --from-changes | sed -n 's/^nescript=//p'
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
    esp32=$(bash .github/scripts/discover-esp32-apps.sh --all)
    pasta=true
    blog=true
    index=true
    nescript=true
    {
      echo "apps=${apps}"
      echo "modules=${modules}"
      echo "rust=${rust}"
      echo "ios=${ios}"
      echo "macos=${macos}"
      echo "esp32=${esp32}"
      echo "pasta=${pasta}"
      echo "blog=${blog}"
      echo "index=${index}"
      echo "nescript=${nescript}"
    } >> "$GITHUB_OUTPUT"
    echo "Testable browser apps: ${apps}"
    echo "Go apps: ${modules}"
    echo "Rust apps: ${rust}"
    echo "iOS apps: ${ios}"
    echo "macOS apps: ${macos}"
    echo "ESP32 firmware: ${esp32}"
    echo "pasta: ${pasta}"
    echo "blog: ${blog}"
    echo "index: ${index}"
    echo "nescript: ${nescript}"
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
  esp32='[]'
  pasta=false
  blog=false
  index=false
  nescript=false
else
  apps=$(printf '%s\n' "$changed" | bash .github/scripts/discover-testable-apps.sh --from-changes)
  modules=$(printf '%s\n' "$changed" | bash .github/scripts/discover-go-modules.sh --from-changes)
  rust=$(printf '%s\n' "$changed" | bash .github/scripts/discover-rust-apps.sh --from-changes)
  ios=$(printf '%s\n' "$changed" | bash .github/scripts/discover-ios-apps.sh --from-changes)
  macos=$(printf '%s\n' "$changed" | bash .github/scripts/discover-macos-apps.sh --from-changes)
  esp32=$(printf '%s\n' "$changed" | bash .github/scripts/discover-esp32-apps.sh --from-changes)
  pasta=$(pasta_from_changes "$changed")
  blog=$(blog_from_changes "$changed")
  index=$(index_from_changes "$changed")
  nescript=$(nescript_from_changes "$changed")
fi

{
  echo "apps=${apps}"
  echo "modules=${modules}"
  echo "rust=${rust}"
  echo "ios=${ios}"
  echo "macos=${macos}"
  echo "esp32=${esp32}"
  echo "pasta=${pasta}"
  echo "blog=${blog}"
  echo "index=${index}"
  echo "nescript=${nescript}"
} >> "$GITHUB_OUTPUT"

echo "Changed paths:"
printf '%s\n' "$changed"
echo "Testable browser apps: ${apps}"
echo "Go apps: ${modules}"
echo "Rust apps: ${rust}"
echo "iOS apps: ${ios}"
echo "macOS apps: ${macos}"
echo "ESP32 firmware: ${esp32}"
echo "pasta: ${pasta}"
echo "blog: ${blog}"
echo "index: ${index}"
echo "nescript: ${nescript}"

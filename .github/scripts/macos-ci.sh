#!/usr/bin/env bash
# Generate and test the macOS apps listed in MACOS_APPS as a JSON array.
# Runs on macOS with Xcode available.
#
# For each app:
#   1. xcodegen generate          (build the .xcodeproj from project.yml)
#   2. bundle install             (fastlane, pinned by the app's Gemfile)
#   3. bundle exec fastlane test  (unit tests on macOS)
#   4. bundle exec fastlane beta  (only when DEPLOY=true → notarize + Sparkle zip)
#   5. publish-macos-sparkle.sh   (GitHub Release + gh-pages appcast)
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# macOS runners ship bash 3.2, which has no `mapfile`/`readarray`.
apps=()
while IFS= read -r app; do
  [ -n "$app" ] && apps+=("$app")
done < <(printf '%s' "${MACOS_APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No macOS apps changed. Nothing to do."
  exit 0
fi

export FASTLANE_XCODEBUILD_SETTINGS_TIMEOUT="${FASTLANE_XCODEBUILD_SETTINGS_TIMEOUT:-120}"
export FASTLANE_XCODEBUILD_SETTINGS_RETRIES="${FASTLANE_XCODEBUILD_SETTINGS_RETRIES:-10}"

deploy="${DEPLOY:-false}"
result=0

for app in "${apps[@]}"; do
  echo "::group::Generate + test ${app}"

  if (
    set -euo pipefail
    cd "$app"
    xcodegen generate
    bundle install
    bundle exec fastlane test
  ); then
    echo "${app}: tests passed"
  else
    echo "::error title=macOS tests failed::${app}: fastlane test"
    result=1
    echo "::endgroup::"
    continue
  fi
  echo "::endgroup::"

  if [ "$deploy" = "true" ]; then
    echo "::group::Ship ${app} (Developer ID + Sparkle)"
    if (
      set -euo pipefail
      cd "$app"
      bundle exec fastlane beta
      RELEASE_DIR="$repo_root/$app/fastlane/release" \
        REPO="${GITHUB_REPOSITORY:?}" \
        GH_TOKEN="${GH_TOKEN:?}" \
        bash "$repo_root/.github/scripts/publish-macos-sparkle.sh"
    ); then
      echo "${app}: release published"
    else
      echo "::error title=macOS release failed::${app}: fastlane beta / publish"
      result=1
    fi
    echo "::endgroup::"
  fi
done

exit "$result"

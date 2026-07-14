#!/usr/bin/env bash
# Generate, test, and (when DEPLOY=true) ship the iOS apps listed in IOS_APPS
# as a JSON array. Runs on macOS with Xcode available.
#
# For each app:
#   1. xcodegen generate                    (build the .xcodeproj from project.yml)
#   2. bundle install                       (fastlane, pinned by the app's Gemfile)
#   3. bundle exec fastlane signing_bootstrap
#      (only when BOOTSTRAP=true — refresh Bundle IDs / match profiles before ship)
#   4. bundle exec fastlane test            (unit + UI tests on a simulator)
#   5. bundle exec fastlane beta            (only when DEPLOY=true → TestFlight)
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# macOS runners ship bash 3.2, which has no `mapfile`/`readarray`. Read the JSON
# array into a plain array with a portable while-read loop instead.
apps=()
while IFS= read -r app; do
  [ -n "$app" ] && apps+=("$app")
done < <(printf '%s' "${IOS_APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No iOS apps changed. Nothing to do."
  exit 0
fi

# `xcodebuild -showBuildSettings` can take well over fastlane's tiny 3s default
# on a cold CI machine; give it room instead of failing the run.
export FASTLANE_XCODEBUILD_SETTINGS_TIMEOUT="${FASTLANE_XCODEBUILD_SETTINGS_TIMEOUT:-120}"
export FASTLANE_XCODEBUILD_SETTINGS_RETRIES="${FASTLANE_XCODEBUILD_SETTINGS_RETRIES:-10}"

# Pick a simulator that actually exists on this runner's Xcode (device names
# change between Xcode versions), unless the caller pinned one.
if [ -z "${IOS_SIM_DEVICE:-}" ]; then
  IOS_SIM_DEVICE=$(
    xcrun simctl list devices available \
      | grep -E '^[[:space:]]+iPhone' \
      | head -1 \
      | sed -E 's/ \(.*//; s/^[[:space:]]+//'
  )
  export IOS_SIM_DEVICE
fi
echo "Using simulator device: ${IOS_SIM_DEVICE:-<none found>}"

deploy="${DEPLOY:-false}"
bootstrap="${BOOTSTRAP:-false}"
result=0

for app in "${apps[@]}"; do
  echo "::group::Generate ${app}"

  if (
    set -euo pipefail
    cd "$app"
    xcodegen generate
    bundle install
  ); then
    echo "${app}: project generated"
  else
    echo "::error title=iOS generate failed::${app}: xcodegen / bundle install"
    result=1
    echo "::endgroup::"
    continue
  fi
  echo "::endgroup::"

  # When a merged change (or needs-ios-bootstrap label) requires refreshed
  # signing assets, re-bootstrap before test/ship so match has the new
  # Bundle IDs / capabilities / profiles.
  if [ "$bootstrap" = "true" ]; then
    echo "::group::Re-bootstrap signing for ${app}"
    if (
      set -euo pipefail
      cd "$app"
      bundle exec fastlane signing_bootstrap
    ); then
      echo "${app}: signing_bootstrap completed"
    else
      echo "::error title=iOS signing bootstrap failed::${app}: fastlane signing_bootstrap"
      result=1
      echo "::endgroup::"
      continue
    fi
    echo "::endgroup::"
  fi

  echo "::group::Test ${app}"
  if (
    set -euo pipefail
    cd "$app"
    bundle exec fastlane test
  ); then
    echo "${app}: tests passed"
  else
    echo "::error title=iOS tests failed::${app}: fastlane test"
    result=1
    echo "::endgroup::"
    continue
  fi
  echo "::endgroup::"

  if [ "$deploy" = "true" ]; then
    echo "::group::Ship ${app} to TestFlight"
    if (
      set -euo pipefail
      cd "$app"
      bundle exec fastlane beta
    ); then
      echo "${app}: uploaded to TestFlight"
    else
      echo "::error title=TestFlight upload failed::${app}: fastlane beta"
      result=1
    fi
    echo "::endgroup::"
  fi
done

exit "$result"

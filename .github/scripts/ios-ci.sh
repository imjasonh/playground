#!/usr/bin/env bash
# Test or ship the iOS apps listed in IOS_APPS as a JSON array. Runs on macOS
# with Xcode available. test.yml runs `ios-ci.sh test`, and ios.yml runs
# `ios-ci.sh ship` on main.
#
# For each app:
#   1. xcodegen generate          (build the .xcodeproj from project.yml)
#   2. bundle install             (fastlane, pinned by the app's Gemfile.lock)
#   3. bundle exec fastlane test  (test: unit + UI tests on a simulator)
#      bundle exec fastlane beta  (ship: upload to TestFlight)
set -uo pipefail

mode="${1:?usage: ios-ci.sh test|ship}"
case "$mode" in
  test) lane=test ;;
  ship) lane=beta ;;
  *)
    echo "usage: ios-ci.sh test|ship" >&2
    exit 2
    ;;
esac

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

result=0

for app in "${apps[@]}"; do
  echo "::group::${mode} ${app}"
  if (
    set -euo pipefail
    cd "$app"
    xcodegen generate
    # setup-ruby already ran bundle install with the lockfile; skip when warm.
    bundle check >/dev/null 2>&1 || bundle install
    bundle exec fastlane "$lane"
  ); then
    echo "${app}: fastlane ${lane} passed"
  else
    echo "::error title=iOS ${mode} failed::${app}: fastlane ${lane}"
    result=1
  fi
  echo "::endgroup::"
done

exit "$result"

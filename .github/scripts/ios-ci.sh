#!/usr/bin/env bash
# Generate, test, and (when DEPLOY=true) ship the iOS apps listed in IOS_APPS
# as a JSON array. Runs on macOS with Xcode available.
#
# For each app:
#   1. xcodegen generate          (build the .xcodeproj from project.yml)
#   2. bundle install             (fastlane, pinned by the app's Gemfile.lock)
#   3. bundle exec fastlane test  (unit + UI tests on a simulator)
#   4. bundle exec fastlane beta  (only when DEPLOY=true → upload to TestFlight)
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

# Stable DerivedData path so the workflow can cache compile products across runs.
export IOS_DERIVED_DATA_PATH="${IOS_DERIVED_DATA_PATH:-$repo_root/ios/.ci-derived-data}"
mkdir -p "$IOS_DERIVED_DATA_PATH"

# Pick a simulator that actually exists on this runner's Xcode (device names
# change between Xcode versions), unless the caller pinned one. Boot it right
# away so CoreSimulator overlaps xcodegen + bundle install.
sim_boot_pid=""
if [ -z "${IOS_SIM_DEVICE:-}" ] || [ -z "${IOS_SIM_UDID:-}" ]; then
  if [ -n "${IOS_SIM_DEVICE:-}" ] && [ -z "${IOS_SIM_UDID:-}" ]; then
    # Caller pinned a name; resolve that device's UDID rather than the first iPhone.
    sim_line=$(
      xcrun simctl list devices available \
        | grep -F "${IOS_SIM_DEVICE} (" \
        | head -1
    )
  else
    sim_line=$(
      xcrun simctl list devices available \
        | grep -E '^[[:space:]]+iPhone' \
        | head -1
    )
  fi
  if [ -z "${IOS_SIM_DEVICE:-}" ]; then
    IOS_SIM_DEVICE=$(
      printf '%s\n' "$sim_line" \
        | sed -E 's/^[[:space:]]+//; s/ \([0-9A-Fa-f-]{36}\).*//'
    )
    export IOS_SIM_DEVICE
  fi
  if [ -z "${IOS_SIM_UDID:-}" ]; then
    IOS_SIM_UDID=$(
      printf '%s\n' "$sim_line" \
        | sed -nE 's/.*\(([0-9A-Fa-f-]{36})\).*/\1/p'
    )
    export IOS_SIM_UDID
  fi
fi
echo "Using simulator device: ${IOS_SIM_DEVICE:-<none found>} (${IOS_SIM_UDID:-no udid})"

if [ -n "${IOS_SIM_UDID:-}" ]; then
  # boot is idempotent when the device is already up; ignore "already booted".
  xcrun simctl boot "$IOS_SIM_UDID" 2>/dev/null || true
  # `wait` only reaps children of this shell, so keep bootstatus in the parent
  # (not inside the per-app subshells below).
  xcrun simctl bootstatus "$IOS_SIM_UDID" -b >/dev/null 2>&1 &
  sim_boot_pid=$!
fi

deploy="${DEPLOY:-false}"
result=0

for app in "${apps[@]}"; do
  echo "::group::Generate + test ${app}"

  if (
    set -euo pipefail
    cd "$app"
    xcodegen generate
    bundle install
  ); then
    echo "${app}: project ready"
  else
    echo "::error title=iOS setup failed::${app}: xcodegen/bundle install"
    result=1
    echo "::endgroup::"
    continue
  fi

  if [ -n "${sim_boot_pid:-}" ]; then
    wait "$sim_boot_pid" || true
    sim_boot_pid=""
  fi

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

if [ -n "${sim_boot_pid:-}" ]; then
  wait "$sim_boot_pid" || true
fi

exit "$result"

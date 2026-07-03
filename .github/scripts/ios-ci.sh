#!/usr/bin/env bash
# Generate, test, and (when DEPLOY=true) ship the iOS apps listed in IOS_APPS
# as a JSON array. Runs on macOS with Xcode available.
#
# For each app:
#   1. xcodegen generate          (build the .xcodeproj from project.yml)
#   2. bundle install             (fastlane, pinned by the app's Gemfile)
#   3. bundle exec fastlane test  (unit + UI tests on a simulator)
#   4. bundle exec fastlane beta  (only when DEPLOY=true → upload to TestFlight)
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t apps < <(printf '%s' "${IOS_APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No iOS apps changed. Nothing to do."
  exit 0
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

#!/usr/bin/env bash
# Tests for deploy-gcp-result.sh, and for the workflow jobs that call it.
# Run: bash .github/scripts/deploy-gcp-result_test.sh
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
script="$script_dir/deploy-gcp-result.sh"
workflow="$script_dir/../workflows/deploy-gcp.yml"
repo_root=$(cd "$script_dir/../.." && pwd)

failures=0
fail() {
  echo "FAIL: $*" >&2
  failures=$((failures + 1))
}

expect_ok() {
  local label="$1"
  shift
  local err
  if ! err=$("$@" 2>&1); then
    fail "$label"
    echo "$err" >&2
  fi
}

expect_fail() {
  local label="$1" needle="$2"
  shift 2
  local err
  if err=$("$@" 2>&1); then
    fail "$label (exit 0)"
    echo "$err" >&2
    return
  fi
  if [[ "$err" != *"$needle"* ]]; then
    fail "$label"
    echo "  missing: $needle" >&2
    echo "  in: $err" >&2
  fi
}

run_result() {
  PREPARE="$1" CHECK="$2" DEPLOY="$3" APPS="$4" EVENT_NAME="$5" REF="$6" \
    bash "$script"
}

apps='["cloudrun-sqlite"]'
main=refs/heads/main
other=refs/heads/topic

expect_ok "nothing to deploy" run_result success skipped skipped '[]' push "$main"
expect_ok "pull request check" run_result success success skipped "$apps" pull_request "$other"
expect_ok "apply on main" run_result success success success "$apps" push "$main"
expect_ok "manual apply on main" run_result success success success "$apps" workflow_dispatch "$main"
expect_ok "manual run off main fails the deploy job" run_result success success failure "$apps" workflow_dispatch "$other"

expect_fail "prepare failed" "prepare failure" \
  run_result failure skipped skipped "$apps" push "$main"
expect_fail "missing apps output" "did not set apps" \
  run_result success skipped skipped '' push "$main"
expect_fail "check skipped while an app is selected" "check skipped" \
  run_result success skipped skipped "$apps" pull_request "$other"
expect_fail "check failed" "check failure" \
  run_result success failure skipped "$apps" push "$main"
expect_fail "deploy skipped on main" "deploy skipped" \
  run_result success success skipped "$apps" push "$main"
expect_fail "deploy ran on a pull request" "pull request" \
  run_result success success success "$apps" pull_request "$other"
expect_fail "deploy skipped off main" "off main was skipped" \
  run_result success success skipped "$apps" workflow_dispatch "$other"
expect_fail "deploy succeeded off main" "off main was success" \
  run_result success success success "$apps" workflow_dispatch "$other"
expect_fail "deploy ran with nothing selected" "no apps" \
  run_result success skipped success '[]' push "$main"

# The check job has to run on pull requests. A job-level if that excludes
# them would skip the job, and a skipped job would make the workflow green.
check_job=$(awk '/^  check:$/,/^  deploy:$/' "$workflow")
if grep -q 'pull_request' <<<"$check_job"; then
  fail "check job excludes pull requests"
fi
if ! grep -q 'deploy-gcp.sh --check' <<<"$check_job"; then
  fail "check job does not run --check"
fi
deploy_job=$(awk '/^  deploy:$/,/^  require:$/' "$workflow")
if ! grep -q 'pull_request' <<<"$deploy_job"; then
  fail "deploy job does not exclude pull requests"
fi
if ! grep -q 'Require main' <<<"$deploy_job"; then
  fail "deploy job does not fail off main"
fi
require_job=$(awk '/^  require:$/,0' "$workflow")
if ! grep -q 'if: always()' <<<"$require_job"; then
  fail "require job can be skipped"
fi
if ! grep -q 'deploy-gcp-result.sh' <<<"$require_job"; then
  fail "require job does not run the result check"
fi
# gcp_deploy_all_path must notice this script, or a change to it selects nothing.
if ! grep -q 'deploy-gcp-result.sh' "$repo_root/.github/scripts/gcp-app.sh"; then
  fail "a change to the result script does not select apps"
fi

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - deploy-gcp-result.sh"

#!/usr/bin/env bash
# Tests for GCP app discovery.
# Run: bash .github/scripts/discover-gcp-apps_test.sh
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
discover="$script_dir/discover-gcp-apps.sh"
changed="$script_dir/discover-changed-gcp.sh"
repo_root=$(cd "$script_dir/../.." && pwd)

failures=0
fail() {
  echo "FAIL: $*" >&2
  failures=$((failures + 1))
}

assert_eq() {
  local got="$1" want="$2" label="$3"
  if [[ "$got" != "$want" ]]; then
    fail "$label"
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
  fi
}

assert_fail() {
  local label="$1"
  shift
  local err
  if err=$("$@" 2>&1); then
    fail "$label (exit 0)"
    echo "$err" >&2
  fi
}

from_changes() {
  printf '%s\n' "$@" | bash "$discover" --from-changes
}

assert_eq "$(bash "$discover" --all)" '["cloudrun-sqlite"]' "--all"
assert_eq "$(from_changes cloudrun-sqlite/main.go)" '["cloudrun-sqlite"]' "app source"
assert_eq "$(from_changes litestream/vfs.go)" '["cloudrun-sqlite"]' "litestream watch"
assert_eq "$(from_changes kanoodle/index.html)" '[]' "unrelated app"
assert_eq "$(from_changes README.md)" '[]' "repo root file"
assert_eq "$(from_changes .github/workflows/deploy-gcp.yml)" '["cloudrun-sqlite"]' "workflow change deploys all"
assert_eq "$(from_changes .github/scripts/deploy-gcp_test.sh)" '[]' "test script does not deploy"
assert_eq "$(printf '' | bash "$discover" --from-changes)" '[]' "empty diff"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

write_manifest() {
  local app="$1" watch="$2"
  mkdir -p "$tmp/$app"
  cat >"$tmp/$app/gcp-deploy.json" <<EOF
{
  "watch": ${watch}
}
EOF
}

write_manifest alpha '["alpha"]'
write_manifest beta '["beta", "shared"]'
assert_eq "$(GCP_DEPLOY_ROOT="$tmp" bash "$discover" --all)" '["alpha","beta"]' "two apps"
assert_eq "$(GCP_DEPLOY_ROOT="$tmp" from_changes shared/file.go)" '["beta"]' "shared prefix"
assert_eq "$(GCP_DEPLOY_ROOT="$tmp" from_changes alpha/main.go beta/main.go)" '["alpha","beta"]' "both apps"
assert_eq "$(GCP_DEPLOY_ROOT="$tmp" from_changes alphabetical/nope.go)" '[]' "prefix is not a substring"

write_manifest gamma '["../secrets"]'
assert_fail "watch prefix escapes the repo" env GCP_DEPLOY_ROOT="$tmp" bash "$discover" --all

rm -rf "$tmp/gamma"
echo '{"service":"nope"}' >"$tmp/alpha/gcp-deploy.json"
assert_fail "rejects an unknown manifest field" env GCP_DEPLOY_ROOT="$tmp" bash "$discover" --all
rm -f "$tmp/alpha/gcp-deploy.json"

mkdir -p "$tmp/Bad_Name"
echo '{}' >"$tmp/Bad_Name/gcp-deploy.json"
assert_fail "rejects a mixed-case directory" env GCP_DEPLOY_ROOT="$tmp" bash "$discover" --all
rm -rf "$tmp/Bad_Name"

# Wrapper: git diffs, manual dispatch, pull requests.
git_root=$(mktemp -d)
git -C "$git_root" init -q -b main
git -C "$git_root" config user.email test@example.com
git -C "$git_root" config user.name test
mkdir -p "$git_root/alpha"
echo '{}' >"$git_root/alpha/gcp-deploy.json"
git -C "$git_root" add alpha/gcp-deploy.json
git -C "$git_root" commit -q -m init
base=$(git -C "$git_root" rev-parse HEAD)
echo touched >"$git_root/alpha/main.go"
git -C "$git_root" add alpha/main.go
git -C "$git_root" commit -q -m change
head=$(git -C "$git_root" rev-parse HEAD)

out=$(mktemp)
EVENT_NAME=push BEFORE_SHA="$base" HEAD_SHA="$head" GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '["alpha"]' "push diff selects the app"

: >"$out"
echo notes >>"$git_root/README.md"
git -C "$git_root" add README.md
git -C "$git_root" commit -q -m readme
readme=$(git -C "$git_root" rev-parse HEAD)
EVENT_NAME=push BEFORE_SHA="$head" HEAD_SHA="$readme" GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '[]' "readme does not select the app"

: >"$out"
EVENT_NAME=workflow_dispatch GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '["alpha"]' "manual dispatch selects all"

: >"$out"
EVENT_NAME=pull_request BEFORE_SHA="$base" HEAD_SHA="$head" GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '["alpha"]' "pull request selects the changed app"

: >"$out"
EVENT_NAME=pull_request BEFORE_SHA="$head" HEAD_SHA="$readme" GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '[]' "pull request with no app changes selects nothing"

assert_fail "pull request without a base SHA fails" \
  env EVENT_NAME=pull_request HEAD_SHA="$head" GCP_DEPLOY_ROOT="$git_root" \
  GITHUB_OUTPUT="$out" bash "$changed"

: >"$out"
EVENT_NAME=push BEFORE_SHA=0000000000000000000000000000000000000000 HEAD_SHA="$head" \
  GCP_DEPLOY_ROOT="$git_root" GITHUB_OUTPUT="$out" bash "$changed" >/dev/null
assert_eq "$(sed -n 's/^apps=//p' "$out")" '["alpha"]' "first push selects all"

# The workflow environment name and the Terraform trust must stay the same.
# Literal ${ } is the text in the workflow and Terraform, not a shell expansion.
# shellcheck disable=SC2016
grep -F -q 'environment: gcp-${{ matrix.app }}' "$repo_root/.github/workflows/deploy-gcp.yml" \
  || fail "workflow environment name"
# shellcheck disable=SC2016
grep -F -q 'gcp-${var.name}' "$repo_root/cloudrun-sqlite/terraform/iam_github.tf" \
  || fail "terraform environment name"
grep -F -q '.github/workflows/deploy-gcp.yml' "$repo_root/gcp/terraform/variables.tf" \
  || fail "terraform workflow path"

rm -rf "$git_root"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-gcp-apps.sh"

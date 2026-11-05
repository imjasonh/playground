#!/usr/bin/env bash
# Tests for discover-rust-apps.sh --from-changes.
# Run: bash .github/scripts/discover-rust-apps_test.sh
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

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

discover() {
  printf '%s\n' "$@" | bash .github/scripts/discover-rust-apps.sh --from-changes
}

all=$(bash .github/scripts/discover-rust-apps.sh --all)

assert_eq "$(discover y/src/lib.rs)" '["y"]' "a change in an app selects that app"
assert_eq "$(discover README.md .github/workflows/test.yml)" '[]' "a change outside an app selects nothing"
assert_eq "$(discover .github/scripts/test-rust-apps.sh)" "$all" "the Rust test script selects every Rust app"
assert_eq "$(discover .github/scripts/check-worker-deploy-build.sh)" "$all" "the Worker build check selects every Rust app"
assert_eq "$(discover .github/wrangler/package.json | jq -c 'index("y") != null and index("life-stl") == null')" "true" \
  "the pinned Wrangler selects Worker apps only"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-rust-apps.sh"

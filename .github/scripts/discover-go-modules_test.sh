#!/usr/bin/env bash
# Tests for discover-go-modules.sh.
# Run: bash .github/scripts/discover-go-modules_test.sh
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
  printf '%s\n' "$@" | bash .github/scripts/discover-go-modules.sh --from-changes
}

has() {
  jq -c --arg m "$2" 'index($m) != null' <<<"$1"
}

all=$(bash .github/scripts/discover-go-modules.sh --all)

assert_eq "$(has "$all" gitdb)" "true" "--all lists a top-level module"
assert_eq "$(has "$all" wehadababyitsaboy/go)" "true" "--all lists a library module in an app's go/ directory"
assert_eq "$(has "$all" wehadababyitsaboy)" "false" "--all leaves out a directory with no go.mod"
assert_eq "$(has "$all" kube/bench)" "false" "--all leaves out other nested modules"

assert_eq "$(discover gitdb/main.go)" '["gitdb"]' "a change in a module selects that module"
assert_eq "$(discover README.md .github/workflows/test.yml)" '[]' "a change outside a module selects nothing"
assert_eq "$(discover wehadababyitsaboy/terraform/main.tf wehadababyitsaboy/README.md)" '[]' \
  "a change beside the go/ module selects nothing"

changed=$(discover wehadababyitsaboy/go/whbiab.go)
assert_eq "$(has "$changed" wehadababyitsaboy/go)" "true" "a change in go/ selects the library module"
for dependent in gitdb ocidb liquid node-image; do
  assert_eq "$(has "$changed" "$dependent")" "true" "a change in go/ selects $dependent, which replaces it"
done
assert_eq "$(has "$changed" kube)" "false" "a change in go/ leaves out modules that don't replace it"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-go-modules.sh"

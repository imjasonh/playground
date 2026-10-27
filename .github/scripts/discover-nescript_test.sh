#!/usr/bin/env bash
# Tests for discover-nescript.sh.
# Run: bash .github/scripts/discover-nescript_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
discover="$script_dir/discover-nescript.sh"

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

from_changes() {
  printf '%s\n' "$@" | bash "$discover" --from-changes | sed -n 's/^nescript=//p'
}

assert_eq "$(bash "$discover" --all)" "nescript=true" "--all"

assert_eq \
  "$(from_changes 'nescript/src/main.rs')" \
  "true" \
  "compiler source"

assert_eq \
  "$(from_changes 'nescript/examples/subway.ne' 'README.md')" \
  "true" \
  "an example among unrelated files"

assert_eq \
  "$(from_changes '.github/workflows/nescript.yml')" \
  "true" \
  "the workflow"

assert_eq \
  "$(from_changes '.github/scripts/discover-nescript.sh')" \
  "true" \
  "the discover script"

assert_eq \
  "$(from_changes '.github/scripts/discover-nescript_test.sh')" \
  "true" \
  "the discover tests"

assert_eq \
  "$(from_changes 'README.md' 'kanoodle/index.html' '.github/workflows/test.yml')" \
  "false" \
  "unrelated files"

assert_eq \
  "$(from_changes '')" \
  "false" \
  "empty input"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-nescript.sh"

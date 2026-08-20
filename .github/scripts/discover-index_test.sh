#!/usr/bin/env bash
# Tests for discover-index.sh.
# Run: bash .github/scripts/discover-index_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
discover="$script_dir/discover-index.sh"

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
  printf '%s\n' "$@" | bash "$discover" --from-changes | sed -n 's/^index=//p'
}

assert_eq "$(bash "$discover" --all)" "index=true" "--all"

assert_eq \
  "$(from_changes '.github/pages/index.html.tmpl')" \
  "true" \
  "index template"

assert_eq \
  "$(from_changes '.github/scripts/render-index.py')" \
  "true" \
  "renderer"

assert_eq \
  "$(from_changes '.github/scripts/render-index_test.py')" \
  "true" \
  "renderer tests"

assert_eq \
  "$(from_changes '.github/scripts/publish-site-index.sh')" \
  "true" \
  "publisher"

assert_eq \
  "$(from_changes '.github/pages/blog-index.html.tmpl' 'README.md' 'kanoodle/index.html')" \
  "false" \
  "blog template, README, and apps do not select the index leg"

assert_eq \
  "$(from_changes '.github/scripts/discover-index.sh' 'pasta/go.mod')" \
  "true" \
  "discover-index.sh itself"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-index.sh"

#!/usr/bin/env bash
# Tests for discover-blog.sh.
# Run: bash .github/scripts/discover-blog_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
discover="$script_dir/discover-blog.sh"

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
  printf '%s\n' "$@" | bash "$discover" --from-changes | sed -n 's/^blog=//p'
}

assert_eq "$(bash "$discover" --all)" "blog=true" "--all"

assert_eq \
  "$(from_changes 'posts/kontain.me-compromise.md')" \
  "true" \
  "post markdown under posts/"

assert_eq \
  "$(from_changes 'posts/docs/platformer.gif')" \
  "true" \
  "post asset under posts/"

assert_eq \
  "$(from_changes '.github/scripts/build-blog.py')" \
  "true" \
  "blog builder"

assert_eq \
  "$(from_changes '.github/pages/blog-post.html.tmpl')" \
  "true" \
  "blog template"

assert_eq \
  "$(from_changes 'pasta/blog-post.md' 'README.md' 'kanoodle/index.html')" \
  "false" \
  "non-posts files do not select the blog leg"

assert_eq \
  "$(from_changes '.github/scripts/discover-blog_test.sh')" \
  "true" \
  "discover-blog_test.sh itself"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-blog.sh"

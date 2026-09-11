#!/usr/bin/env bash
# Tests for its-not-jaws-should-play.sh.
# Run: bash .github/scripts/its-not-jaws-should-play_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
gate="$script_dir/its-not-jaws-should-play.sh"

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

decide() {
  printf '%s\n' "$@" | bash "$gate"
}

assert_eq "$(decide)" "play=false" "empty diff"

assert_eq \
  "$(decide 'its-not-jaws/blog-post.md')" \
  "play=false" \
  "blog post only"

assert_eq \
  "$(decide 'its-not-jaws/README.md' 'its-not-jaws/DESIGN.md' 'its-not-jaws/GAME.md')" \
  "play=false" \
  "docs only"

assert_eq \
  "$(decide 'its-not-jaws/tests/harness.test.ts')" \
  "play=false" \
  "tests only"

assert_eq \
  "$(decide '.github/workflows/its-not-jaws.yml')" \
  "play=false" \
  "workflow only"

# The cited posts-catalog pull request added a post under its-not-jaws/
# and must not play a live game.
assert_eq \
  "$(decide \
    '.github/pages/blog-index.html.tmpl' \
    '.github/scripts/build-blog.py' \
    '.github/workflows/deploy.yml' \
    'AGENTS.md' \
    'its-not-jaws/blog-post.md' \
    'pasta/blog-post.md')" \
  "play=false" \
  "posts catalog pull request"

assert_eq \
  "$(decide 'its-not-jaws/src/harness.ts')" \
  "play=true" \
  "harness source"

assert_eq \
  "$(decide 'its-not-jaws/src/games/its-not-jaws.ts')" \
  "play=true" \
  "nested source"

assert_eq \
  "$(decide 'its-not-jaws/package.json')" \
  "play=true" \
  "package.json"

assert_eq \
  "$(decide 'its-not-jaws/package-lock.json')" \
  "play=true" \
  "package-lock.json"

assert_eq \
  "$(decide 'its-not-jaws/tsconfig.json')" \
  "play=true" \
  "tsconfig.json"

assert_eq \
  "$(decide 'its-not-jaws/blog-post.md' 'its-not-jaws/src/cli.ts')" \
  "play=true" \
  "post plus harness source"

assert_eq \
  "$(printf 'its-not-jaws/src/limits.ts\r\n' | bash "$gate")" \
  "play=true" \
  "CRLF path"

if [ "$failures" -ne 0 ]; then
  echo "$failures assertion(s) failed" >&2
  exit 1
fi

echo "ok"

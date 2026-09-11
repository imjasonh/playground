#!/usr/bin/env bash
# Decide whether an It's Not Jaws pull request should spend Cursor tokens
# on a live game.
#
# Harness paths (play):
#   its-not-jaws/src/**
#   its-not-jaws/package.json
#   its-not-jaws/package-lock.json
#   its-not-jaws/tsconfig.json
#
# Docs, blog-post.md, tests, and the workflow file do not play a game.
# A posts catalog pull request that only adds its-not-jaws/blog-post.md
# must print play=false.
#
# Usage: print changed paths on stdin. Writes play=true or play=false.
set -euo pipefail

is_harness_path() {
  case "$1" in
    its-not-jaws/src/*) return 0 ;;
    its-not-jaws/package.json|its-not-jaws/package-lock.json|its-not-jaws/tsconfig.json) return 0 ;;
  esac
  return 1
}

while IFS= read -r path || [ -n "$path" ]; do
  # git diff can emit a trailing CR on some checkouts.
  path="${path%$'\r'}"
  [ -z "$path" ] && continue
  if is_harness_path "$path"; then
    printf 'play=true\n'
    exit 0
  fi
done

printf 'play=false\n'

#!/usr/bin/env bash
# Decide whether the posts catalog CI / preview legs should run.
#
# Usage:
#   discover-blog.sh --all
#     Always enable (first push / full suite).
#   discover-blog.sh --from-changes [path...]
#     Enable when a blog-post.md file or the posts builder / templates
#     changed. Paths may also be piped on stdin.
set -euo pipefail

emit() {
  printf 'blog=%s\n' "$1"
}

is_blog_path() {
  case "$1" in
    blog-post.md|*/blog-post.md) return 0 ;;
    .github/scripts/build-blog.py|.github/scripts/build-blog_test.py) return 0 ;;
    .github/scripts/test-blog.sh|.github/scripts/discover-blog.sh) return 0 ;;
    .github/pages/blog-index.html.tmpl|.github/pages/blog-post.html.tmpl) return 0 ;;
  esac
  return 1
}

from_changes() {
  local path
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    if is_blog_path "$path"; then
      echo true
      return 0
    fi
  done
  echo false
}

case "${1:-}" in
  --all)
    emit true
    ;;
  --from-changes)
    shift
    if [ "$#" -gt 0 ]; then
      printf '%s\n' "$@" | from_changes | { read -r v; emit "$v"; }
    else
      from_changes | { read -r v; emit "$v"; }
    fi
    ;;
  *)
    echo "usage: $0 --all | --from-changes [path...]" >&2
    exit 2
    ;;
esac

#!/usr/bin/env bash
# Decide whether the Pages home-page index CI / preview legs should run.
#
# Usage:
#   discover-index.sh --all
#     Always enable (first push / full suite).
#   discover-index.sh --from-changes [path...]
#     Enable when the shared index template, renderer, or publisher
#     changed. Paths may also be piped on stdin.
set -euo pipefail

emit() {
  printf 'index=%s\n' "$1"
}

is_index_path() {
  case "$1" in
    .github/pages/index.html.tmpl) return 0 ;;
    .github/scripts/render-index.py|.github/scripts/render-index_test.py) return 0 ;;
    .github/scripts/publish-site-index.sh) return 0 ;;
    .github/scripts/test-index.sh|.github/scripts/discover-index.sh|.github/scripts/discover-index_test.sh) return 0 ;;
  esac
  return 1
}

from_changes() {
  local path
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    if is_index_path "$path"; then
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

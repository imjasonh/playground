#!/usr/bin/env bash
# Decide whether the pasta CI leg should run for a change set.
#
# Usage:
#   discover-pasta.sh --all
#     Always enable the pasta leg (first push / full suite).
#   discover-pasta.sh --from-changes [path...]
#     Enable when pasta itself, .pasta/ rules, the pasta CI scripts, or
#     any lintable source file changed. Paths may also be piped on stdin.
set -euo pipefail

emit() {
  # GitHub Actions output: pasta=true|false
  printf 'pasta=%s\n' "$1"
}

is_lintable() {
  case "$1" in
    *.go|*.js|*.mjs|*.cjs|*.jsx|*.ts|*.tsx|*.rs|*.swift|*.sh|*.bash|*.yml|*.yaml|*.html|*.htm|*.css|*.cue)
      return 0
      ;;
  esac
  return 1
}

from_changes() {
  local path
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    case "$path" in
      pasta/*|.pasta/*|.github/scripts/test-pasta.sh|.github/scripts/discover-pasta.sh)
        echo true
        return 0
        ;;
    esac
    if is_lintable "$path"; then
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

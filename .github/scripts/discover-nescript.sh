#!/usr/bin/env bash
# Decide whether test.yml's nescript job should run its benches, ROM diff,
# jsnes goldens, GIF check, and Mesen probe.
#
# Usage:
#   discover-nescript.sh --all
#     Always enable (a push with no parent commit).
#   discover-nescript.sh --from-changes [path...]
#     Enable when nescript/ changed.
#     Paths may also be piped on stdin.
set -euo pipefail

emit() {
  printf 'nescript=%s\n' "$1"
}

is_nescript_path() {
  case "$1" in
    nescript/*) return 0 ;;
  esac
  return 1
}

from_changes() {
  local path
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    if is_nescript_path "$path"; then
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

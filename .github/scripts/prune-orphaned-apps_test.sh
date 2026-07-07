#!/usr/bin/env bash
# Tests for prune-orphaned-apps.sh. Run directly:
#   bash .github/scripts/prune-orphaned-apps_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
prune="$script_dir/prune-orphaned-apps.sh"

failures=0
assert_exists() {
  if [[ ! -e "$1" ]]; then
    echo "FAIL: expected to exist: $1" >&2
    failures=$((failures + 1))
  fi
}
assert_absent() {
  if [[ -e "$1" ]]; then
    echo "FAIL: expected to be pruned: $1" >&2
    failures=$((failures + 1))
  fi
}

make_app() {
  mkdir -p "$1"
  echo "<!doctype html>" > "$1/index.html"
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

source_dir="$work/source"
site_dir="$work/site"

# Source has webrtc + kanoodle (kanoodle also has a nested dir; webrtc renamed
# from linkchat). A source dir without index.html is not an app.
make_app "$source_dir/webrtc"
make_app "$source_dir/kanoodle"
mkdir -p "$source_dir/gitdb"            # Go app: no index.html, not published
echo "package main" > "$source_dir/gitdb/main.go"
mkdir -p "$source_dir/.github/scripts"  # hidden: ignored

# Published site still carries the old linkchat app plus a preview and root
# index that must survive.
make_app "$site_dir/webrtc"
make_app "$site_dir/kanoodle"
make_app "$site_dir/linkchat"           # orphan: renamed away in source
make_app "$site_dir/preview/pr-42"      # preview app must never be pruned
echo "<!doctype html>" > "$site_dir/index.html"
mkdir -p "$site_dir/.git"               # hidden: ignored
echo "ref" > "$site_dir/.git/HEAD"

output="$(bash "$prune" "$site_dir" "$source_dir")"

assert_absent "$site_dir/linkchat"
assert_exists "$site_dir/webrtc/index.html"
assert_exists "$site_dir/kanoodle/index.html"
assert_exists "$site_dir/index.html"
assert_exists "$site_dir/preview/pr-42/index.html"
assert_exists "$site_dir/.git/HEAD"

if [[ "$output" != *"Pruning orphaned app: linkchat"* ]]; then
  echo "FAIL: expected linkchat prune message, got: $output" >&2
  failures=$((failures + 1))
fi

# Re-running is a no-op once orphans are gone.
output2="$(bash "$prune" "$site_dir" "$source_dir")"
if [[ "$output2" != *"No orphaned apps to prune."* ]]; then
  echo "FAIL: expected no-op on second run, got: $output2" >&2
  failures=$((failures + 1))
fi

if ((failures > 0)); then
  echo "$failures test(s) failed." >&2
  exit 1
fi
echo "All prune-orphaned-apps tests passed."

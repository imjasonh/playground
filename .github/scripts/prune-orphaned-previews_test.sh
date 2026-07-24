#!/usr/bin/env bash
# Tests for prune-orphaned-previews.sh. Run directly:
#   bash .github/scripts/prune-orphaned-previews_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
prune="$script_dir/prune-orphaned-previews.sh"

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

make_preview() {
  local dir="$1"
  local number="$2"
  mkdir -p "$dir"
  printf '{"number": %s, "title": "PR %s", "apps": ["hello"]}\n' "$number" "$number" \
    > "$dir/preview.json"
  echo "<!doctype html>" > "$dir/index.html"
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

site_dir="$work/site"
make_preview "$site_dir/preview/pr-10" 10
make_preview "$site_dir/preview/pr-20" 20
make_preview "$site_dir/preview/pr-30" 30
mkdir -p "$site_dir/preview/not-a-pr"
echo "keep" > "$site_dir/preview/not-a-pr/marker"
mkdir -p "$site_dir/hello"
echo "<!doctype html>" > "$site_dir/hello/index.html"

# Only PR 20 is still open; 10 and 30 should be pruned. Non-pr-* entries stay.
output="$(bash "$prune" "$site_dir" 20)"

assert_absent "$site_dir/preview/pr-10"
assert_exists "$site_dir/preview/pr-20/preview.json"
assert_absent "$site_dir/preview/pr-30"
assert_exists "$site_dir/preview/not-a-pr/marker"
assert_exists "$site_dir/hello/index.html"

if [[ "$output" != *"Pruning orphaned preview: pr-10"* ]]; then
  echo "FAIL: expected pr-10 prune message, got: $output" >&2
  failures=$((failures + 1))
fi
if [[ "$output" != *"Pruning orphaned preview: pr-30"* ]]; then
  echo "FAIL: expected pr-30 prune message, got: $output" >&2
  failures=$((failures + 1))
fi

# Re-running with the same keep set is a no-op.
output2="$(bash "$prune" "$site_dir" 20)"
if [[ "$output2" != *"No orphaned previews to prune."* ]]; then
  echo "FAIL: expected no-op on second run, got: $output2" >&2
  failures=$((failures + 1))
fi

# Passing no open PRs prunes everything under preview/pr-* and removes empty
# preview/ when only pr-* dirs existed (not-a-pr keeps preview/ alive here).
bash "$prune" "$site_dir" >/dev/null
assert_absent "$site_dir/preview/pr-20"
assert_exists "$site_dir/preview/not-a-pr/marker"

# When preview/ only had pr-* dirs, pruning the last one removes preview/.
site2="$work/site2"
make_preview "$site2/preview/pr-1" 1
output3="$(bash "$prune" "$site2")"
assert_absent "$site2/preview"
if [[ "$output3" != *"Removed empty preview directory."* ]]; then
  echo "FAIL: expected empty preview/ removal, got: $output3" >&2
  failures=$((failures + 1))
fi

# Invalid args.
if bash "$prune" "$site_dir" abc 2>/dev/null; then
  echo "FAIL: expected invalid PR number to fail" >&2
  failures=$((failures + 1))
fi

if ((failures > 0)); then
  echo "$failures test(s) failed." >&2
  exit 1
fi
echo "All prune-orphaned-previews tests passed."

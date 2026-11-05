#!/usr/bin/env bash
# Tests for prune-go-caches.sh --build and check-cache-size.sh.
# Run: bash .github/scripts/prune-go-caches_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
prune="$script_dir/prune-go-caches.sh"
check="$script_dir/check-cache-size.sh"

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

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# entry writes a build cache entry of SIZE bytes, last used DAYS_AGO days ago.
entry() {
  local name="$1" size="$2" days_ago="$3"
  mkdir -p "$tmp/cache/${name:0:2}"
  head -c "$size" /dev/zero >"$tmp/cache/${name:0:2}/$name"
  touch -d "${days_ago} days ago" "$tmp/cache/${name:0:2}/$name"
}

entry aa00-d 400 5
entry bb00-d 300 4
entry cc00-d 200 3
entry dd00-a 100 2
entry ee00-d 100 1
echo 1700000000 >"$tmp/cache/trim.txt"
echo readme >"$tmp/cache/README"
mkdir -p "$tmp/cache/fuzz"
head -c 500 /dev/zero >"$tmp/cache/fuzz/corpus"

GOCACHE="$tmp/cache" GO_BUILD_CACHE_BUDGET=450 bash "$prune" --build >/dev/null

remaining=$(cd "$tmp/cache" && find . -mindepth 2 -type f -path './[0-9a-f][0-9a-f]/*' | sort | tr '\n' ' ')
assert_eq "$remaining" "./cc/cc00-d ./dd/dd00-a ./ee/ee00-d " \
  "deletes the least recently used entries until the rest fit the budget"
assert_eq "$(ls "$tmp/cache/aa" | wc -l)" "0" "an emptied subdirectory stays"
assert_eq "$(cat "$tmp/cache/trim.txt")" "1700000000" "trim.txt is kept"
assert_eq "$(cat "$tmp/cache/README")" "readme" "README is kept"
assert_eq "$(stat -c %s "$tmp/cache/fuzz/corpus")" "500" "fuzz/ is kept"

GOCACHE="$tmp/cache" GO_BUILD_CACHE_BUDGET=1000 bash "$prune" --build >/dev/null
remaining=$(cd "$tmp/cache" && find . -mindepth 2 -type f -path './[0-9a-f][0-9a-f]/*' | sort | tr '\n' ' ')
assert_eq "$remaining" "./cc/cc00-d ./dd/dd00-a ./ee/ee00-d " \
  "a cache within budget is unchanged"

GOCACHE="$tmp/missing" bash "$prune" --build >/dev/null
assert_eq "$?" "0" "a missing cache directory is not an error"

mkdir -p "$tmp/sizes"
head -c 300 /dev/zero >"$tmp/sizes/a"
head -c 300 /dev/zero >"$tmp/sizes/b"
if bash "$check" 1000 "$tmp/sizes/a" "$tmp/sizes/b" "$tmp/sizes/none" >/dev/null; then
  status=0
else
  status=$?
fi
assert_eq "$status" "0" "paths within budget pass; a missing path counts as empty"

if bash "$check" 500 "$tmp/sizes/a" "$tmp/sizes/b" >/dev/null; then
  status=0
else
  status=$?
fi
assert_eq "$status" "1" "paths over budget fail"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - prune-go-caches.sh"

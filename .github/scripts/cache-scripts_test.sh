#!/usr/bin/env bash
# Tests for trim-go-build-cache.sh, check-cache-size.sh, and
# delete-superseded-caches.sh.
# Run: bash .github/scripts/cache-scripts_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
trim="$script_dir/trim-go-build-cache.sh"
check="$script_dir/check-cache-size.sh"
supersede="$script_dir/delete-superseded-caches.sh"

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

GOCACHE="$tmp/cache" GO_BUILD_CACHE_BUDGET=450 bash "$trim" >/dev/null

remaining=$(cd "$tmp/cache" && find . -mindepth 2 -type f -path './[0-9a-f][0-9a-f]/*' | sort | tr '\n' ' ')
assert_eq "$remaining" "./cc/cc00-d ./dd/dd00-a ./ee/ee00-d " \
  "deletes the least recently used entries until the rest fit the budget"
assert_eq "$(ls "$tmp/cache/aa" | wc -l)" "0" "an emptied subdirectory stays"
assert_eq "$(cat "$tmp/cache/trim.txt")" "1700000000" "trim.txt is kept"
assert_eq "$(cat "$tmp/cache/README")" "readme" "README is kept"
assert_eq "$(stat -c %s "$tmp/cache/fuzz/corpus")" "500" "fuzz/ is kept"

GOCACHE="$tmp/cache" GO_BUILD_CACHE_BUDGET=1000 bash "$trim" >/dev/null
remaining=$(cd "$tmp/cache" && find . -mindepth 2 -type f -path './[0-9a-f][0-9a-f]/*' | sort | tr '\n' ' ')
assert_eq "$remaining" "./cc/cc00-d ./dd/dd00-a ./ee/ee00-d " \
  "a cache within budget is unchanged"

GOCACHE="$tmp/missing" bash "$trim" >/dev/null
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

# A stub gh serves `gh cache list` and `gh cache delete` from a JSON file and
# logs each delete.
mkdir -p "$tmp/bin"
cat >"$tmp/bin/gh" <<'STUB'
#!/usr/bin/env bash
case "$1 $2" in
  "cache list")
    prefix=""
    while (($# > 0)); do
      [[ "$1" == "--key" ]] && prefix="$2"
      shift
    done
    jq -c --arg p "$prefix" '[.[] | select(.key | startswith($p))]' "$STUB_CACHES"
    ;;
  "cache delete")
    echo "$3" >>"$STUB_DELETED"
    ;;
  *)
    echo "unexpected: $*" >&2
    exit 1
    ;;
esac
STUB
chmod +x "$tmp/bin/gh"
export STUB_CACHES="$tmp/caches.json" STUB_DELETED="$tmp/deleted"

cat >"$STUB_CACHES" <<'JSON'
[
  {"id": 1, "key": "go-Linux-1.26-aaa", "createdAt": "2026-01-01T00:00:00Z"},
  {"id": 2, "key": "go-build-Linux-1.27-old", "createdAt": "2026-01-02T00:00:00Z"},
  {"id": 3, "key": "go-build-Linux-1.27-mid", "createdAt": "2026-01-03T00:00:00Z"},
  {"id": 4, "key": "go-build-Linux-1.27-new", "createdAt": "2026-01-04T00:00:00Z"},
  {"id": 5, "key": "go-build-Linux-1.27-newer", "createdAt": "2026-01-05T00:00:00Z"},
  {"id": 6, "key": "npm-cacache-Linux-old", "createdAt": "2026-01-01T00:00:00Z"}
]
JSON

deleted() {
  if [[ -f "$STUB_DELETED" ]]; then sort -n "$STUB_DELETED" | tr '\n' ' '; fi
}

PATH="$tmp/bin:$PATH" bash "$supersede" go-build-Linux-1.27-new go-build-Linux- go-Linux- >/dev/null
assert_eq "$(deleted)" "1 2 3 " \
  "deletes older entries of each prefix, keeps the new entry, a newer entry, and other families"

rm -f "$STUB_DELETED"
PATH="$tmp/bin:$PATH" bash "$supersede" go-build-Linux-1.27-missing go-build-Linux- >/dev/null
assert_eq "$(deleted)" "" "deletes nothing when the key to keep does not exist"

rm -f "$STUB_DELETED"
PATH="$tmp/bin:$PATH" bash "$supersede" "" go-build-Linux- >/dev/null
assert_eq "$(deleted)" "2 3 4 5 " "an empty key to keep deletes every entry of the family"

rm -f "$STUB_DELETED"
PATH="$tmp/bin:$PATH" bash "$supersede" "" "" >/dev/null
assert_eq "$(deleted)" "" "an empty prefix matches nothing"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - cache scripts"

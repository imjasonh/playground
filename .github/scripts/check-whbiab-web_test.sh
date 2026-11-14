#!/usr/bin/env bash
# Tests for check-whbiab-web.sh and wehadababyitsaboy/web/whbiab.js, and a
# check of the real browser apps.
# Run: bash .github/scripts/check-whbiab-web_test.sh
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
check="$repo_root/.github/scripts/check-whbiab-web.sh"

failures=0
expect() {
  local label="$1" want="$2" got="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label (got $got, want $want)" >&2
    failures=$((failures + 1))
  fi
}

passes() {
  if bash "$check" "$1" >/dev/null 2>&1; then echo pass; else echo fail; fi
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

mkdir -p "$tmp/wehadababyitsaboy/web" "$tmp/demo" "$tmp/other" "$tmp/csp" "$tmp/.hidden"
echo '// canonical' >"$tmp/wehadababyitsaboy/web/whbiab.js"
printf '<html>\n<body>\n  <h1>demo</h1>\n</body>\n</html>\n' >"$tmp/demo/index.html"
printf '<html>\n<body>\n</body>\n</html>\n' >"$tmp/other/index.html"
echo '<html><body></body></html>' >"$tmp/.hidden/index.html"
cat >"$tmp/csp/index.html" <<'HTML'
<html>
<head>
  <meta
    http-equiv="Content-Security-Policy"
    content="default-src 'none'; script-src 'self'; img-src 'self' blob:"
  />
</head>
<body>
</body>
</html>
HTML

expect "an app with no copy and no tag fails" fail "$(passes "$tmp")"

bash "$check" --fix "$tmp" >/dev/null 2>&1 || true
expect "--fix copies the script" "// canonical" "$(cat "$tmp/demo/whbiab.js")"
expect "--fix adds the tag with the app name" 1 \
  "$(grep -c '^  <script src="whbiab.js" data-app="demo"></script>$' "$tmp/demo/index.html")"
expect "--fix indents the tag to match </body>" 1 \
  "$(grep -c '^  <script src="whbiab.js" data-app="other"></script>$' "$tmp/other/index.html")"
expect "--fix skips hidden directories" 0 "$(ls "$tmp/.hidden" | grep -c whbiab || true)"
expect "a CSP that blocks the image fails" fail "$(passes "$tmp")"

sed -i "s#img-src 'self' blob:#img-src 'self' blob: https://storage.googleapis.com#" "$tmp/csp/index.html"
expect "a CSP that allows the image passes" pass "$(passes "$tmp")"

bash "$check" --fix "$tmp" >/dev/null 2>&1
expect "--fix twice adds one tag" 1 "$(grep -c 'whbiab.js' "$tmp/demo/index.html")"

echo '// edited' >"$tmp/demo/whbiab.js"
expect "a modified copy fails" fail "$(passes "$tmp")"
bash "$check" --fix "$tmp" >/dev/null 2>&1
expect "--fix restores a modified copy" pass "$(passes "$tmp")"

sed -i 's#data-app="other"#data-app="wrong"#' "$tmp/other/index.html"
expect "a tag with the wrong app name fails" fail "$(passes "$tmp")"

expect "the real browser apps record visits" pass "$(passes "$repo_root")"

node --test "$repo_root/wehadababyitsaboy/web/whbiab.test.js" >/dev/null ||
  {
    echo "FAIL: node --test wehadababyitsaboy/web/whbiab.test.js" >&2
    failures=$((failures + 1))
  }

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - check-whbiab-web.sh"

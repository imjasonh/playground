#!/usr/bin/env bash
# Check that every browser app records its visits in the wehadababyitsaboy
# usage bucket, or fix the apps that don't.
#
# A browser app is a top-level directory with an index.html. Each one needs:
#   - whbiab.js, a symbolic link to wehadababyitsaboy/web/whbiab.js. The deploy
#     and preview workflows copy each app directory with cp -L, so the
#     published app holds the file itself.
#   - one <script src="whbiab.js" data-app="DIR"></script> in index.html, where
#     DIR is the app's directory name
#   - a Content-Security-Policy, if index.html sets one, that lets the script
#     load and lets the page request an image from storage.googleapis.com
#
# Usage:
#   check-whbiab-web.sh [--fix] [ROOT]
#     ROOT is the repository root. Default: the checkout this script is in.
#     --fix links whbiab.js into each app and adds the script tag before
#     </body>. It never edits a Content-Security-Policy.
set -euo pipefail

fix=false
if [[ "${1:-}" == "--fix" ]]; then
  fix=true
  shift
fi

root=${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}
canonical="$root/wehadababyitsaboy/web/whbiab.js"
link_target="../wehadababyitsaboy/web/whbiab.js"
if [[ ! -f "$canonical" ]]; then
  echo "missing $canonical" >&2
  exit 2
fi

failures=0
fail() {
  echo "FAIL: $1" >&2
  failures=$((failures + 1))
}

# csp_of prints the Content-Security-Policy that index.html $1 sets in a meta
# tag, or nothing.
csp_of() {
  tr '\n' ' ' <"$1" |
    grep -oE 'Content-Security-Policy"[^>]*content="[^"]*"' |
    head -1 || true
}

# directive prints CSP $2's $1 directive, or its default-src when it has no $1,
# which is the directive the browser applies.
directive() {
  grep -oE "$1[^;\"]*" <<<"$2" || grep -oE "default-src[^;\"]*" <<<"$2" || true
}

for dir in "$root"/*/; do
  app=$(basename "$dir")
  [[ "$app" == .* ]] && continue
  index="$dir/index.html"
  [[ -f "$index" ]] || continue

  tag="<script src=\"whbiab.js\" data-app=\"$app\"></script>"

  if $fix; then
    ln -sfn "$link_target" "$dir/whbiab.js"
    if ! grep -qF "$tag" "$index"; then
      awk -v tag="$tag" '
        !done && /<\/body>/ {
          match($0, /^[ \t]*/)
          print substr($0, 1, RLENGTH) "  " tag
          done = 1
        }
        { print }
      ' "$index" >"$index.tmp"
      mv "$index.tmp" "$index"
    fi
  fi

  if [[ ! -L "$dir/whbiab.js" || "$(readlink "$dir/whbiab.js")" != "$link_target" ]]; then
    fail "$app: whbiab.js must be a symbolic link to $link_target"
  fi
  if [[ "$(grep -cF "$tag" "$index")" != 1 ]]; then
    fail "$app: index.html needs exactly one $tag"
  fi

  csp=$(csp_of "$index")
  if [[ -n "$csp" ]]; then
    if ! grep -qE "storage\.googleapis\.com|\*|https:" <<<"$(directive img-src "$csp")"; then
      fail "$app: the Content-Security-Policy img-src must allow https://storage.googleapis.com"
    fi
    if ! grep -qF "'self'" <<<"$(directive script-src "$csp")"; then
      fail "$app: the Content-Security-Policy script-src must allow 'self'"
    fi
  fi
done

if ((failures > 0)); then
  echo "$failures problem(s). Run: bash .github/scripts/check-whbiab-web.sh --fix" >&2
  exit 1
fi
echo "ok - every browser app records its visits"

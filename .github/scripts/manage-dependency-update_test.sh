#!/usr/bin/env bash
# Tests for manage-dependency-update.sh change detection. Run directly:
#   bash .github/scripts/manage-dependency-update_test.sh
set -euo pipefail

script="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/manage-dependency-update.sh"

failures=0
expect() {
  if [[ "$2" != "$3" ]]; then
    echo "FAIL: $1: want [$2], got [$3]" >&2
    failures=$((failures + 1))
  fi
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
export GITHUB_OUTPUT="$work/output"

# No app vendors anything, so the */vendor/** glob matches no file.
cd "$work"
git init -q -b main repo
cd repo
git config user.name test
git config user.email test@example.com
mkdir gomod jsapp worker .github .github/wrangler
echo 'module gomod' > gomod/go.mod
echo '{"devDependencies":{"wrangler":"4.0.0"}}' > .github/wrangler/package.json
echo '{}' > jsapp/package.json
echo '{}' > jsapp/package-lock.json
echo '[package]' > worker/Cargo.toml
echo '# v1' > worker/Cargo.lock
echo 'package.json' > worker/.gitignore
echo 'fn main() {}' > worker/main.rs
git add -A
git commit -qm init

detect() {
  : > "$GITHUB_OUTPUT"
  bash "$script" detect-changes > /dev/null
  sed -n 's/^has_changes=//p' "$GITHUB_OUTPUT"
}
staged() {
  git diff --cached --name-status | tr '\t\n' ' ' | sed 's/ $//'
}
reset_tree() {
  git reset -q --hard
  git clean -qfdx
}

expect "clean tree" false "$(detect)"

# A source edit and the ignored package.json that worker-build needs are not
# dependency changes.
echo 'fn main() { }' > worker/main.rs
echo '{"dependencies":{"wrangler":"4.107.0"}}' > worker/package.json
expect "source edit and ignored decoy" false "$(detect)"
expect "source edit and ignored decoy staged" "" "$(staged)"
reset_tree

echo '# v2' > worker/Cargo.lock
expect "lockfile bump" true "$(detect)"
expect "lockfile bump staged" "M worker/Cargo.lock" "$(staged)"
reset_tree

echo '{"devDependencies":{"wrangler":"4.1.0"}}' > .github/wrangler/package.json
expect "wrangler bump" true "$(detect)"
expect "wrangler bump staged" "M .github/wrangler/package.json" "$(staged)"
reset_tree

mkdir newmod
echo 'module newmod' > newmod/go.mod
rm jsapp/package-lock.json
expect "added and deleted files" true "$(detect)"
expect "added and deleted files staged" "D jsapp/package-lock.json A newmod/go.mod" "$(staged)"
reset_tree

# With nothing to commit, open-success-pr must fail instead of reporting
# success.
if bash "$script" open-success-pr > /dev/null 2>&1; then
  echo "FAIL: open-success-pr succeeded with nothing staged" >&2
  failures=$((failures + 1))
fi

if [[ "$failures" -ne 0 ]]; then
  echo "$failures failure(s)" >&2
  exit 1
fi
echo "PASS"

#!/usr/bin/env bash
# Tests for update-litestream.sh pull. Run directly:
#   bash .github/scripts/update-litestream_test.sh
set -euo pipefail

script="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/update-litestream.sh"

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
unset GH_TOKEN GITHUB_REPOSITORY
export LITESTREAM_UPSTREAM_URL="$work/upstream"
branch=automation/litestream-update

commit_upstream() {
  printf 'package litestream\n\nconst %s = %s\n' "$2" "$3" > "$work/upstream/$1"
  git -C "$work/upstream" commit -qam "upstream: $2 = $3"
}

# A stand-in for benbjohnson/litestream.
git init -q -b main "$work/upstream"
git -C "$work/upstream" config user.name upstream
git -C "$work/upstream" config user.email upstream@example.com
printf 'package litestream\n\nconst A = 1\n' > "$work/upstream/a.go"
printf 'package litestream\n\nconst B = 1\n' > "$work/upstream/b.go"
git -C "$work/upstream" add -A
git -C "$work/upstream" commit -qm "upstream: A = 1, B = 1"

# The monorepo: the subtree plus a local patch to b.go, pushed to a bare origin.
git init -q --bare -b main "$work/origin.git"
git init -q -b main "$work/repo"
cd "$work/repo"
git config user.name test
git config user.email test@example.com
echo '# repo' > README.md
git add -A
git commit -qm init
git subtree add -q --prefix=litestream "$work/upstream" main --squash > /dev/null 2>&1
printf 'package litestream\n\nconst B = 2 // patched\n' > litestream/b.go
git commit -qam "litestream: patch B"
git remote add origin "$work/origin.git"
git push -q origin main

pull() {
  : > "$GITHUB_OUTPUT"
  if ! bash "$script" pull > "$work/pull.log" 2>&1; then
    cat "$work/pull.log" >&2
    echo "pull exited with an error"
    return
  fi
  sed -n 's/^result=//p' "$GITHUB_OUTPUT"
}
output() {
  sed -n "s/^$1=//p" "$GITHUB_OUTPUT"
}
last_import() {
  git log -1 --format=%B "$(git log --grep='^git-subtree-dir: litestream$' --format=%H -1)" |
    sed -n 's/^git-subtree-split: //p'
}
reset_repo() {
  git checkout -q main
  git reset -q --hard origin/main
  git branch -qD "$branch" 2>/dev/null || true
}

expect "unchanged" unchanged "$(pull)"
expect "unchanged stays on main" main "$(git branch --show-current)"

commit_upstream a.go A 2
expect "clean merge" merged "$(pull)"
expect "clean merge branch" "$branch" "$(git branch --show-current)"
expect "clean merge keeps the patch" "const B = 2 // patched" "$(sed -n 3p litestream/b.go)"
expect "clean merge takes upstream" "const A = 2" "$(sed -n 3p litestream/a.go)"
expect "clean merge records the import" "$(git -C "$work/upstream" rev-parse HEAD)" "$(last_import)"
expect "clean merge upstream output" "$(git -C "$work/upstream" rev-parse HEAD)" "$(output upstream)"
reset_repo

commit_upstream b.go B 3
expect "conflict" conflict "$(pull)"
expect "conflict files" "litestream/b.go" "$(sed -n '/^conflicts<<EOF$/,/^EOF$/p' "$GITHUB_OUTPUT" | sed '1d;$d')"
expect "conflict markers committed" 1 "$(git show HEAD:litestream/b.go | grep -c '^<<<<<<<')"
expect "conflict merge finished" "" "$(git rev-parse -q --verify MERGE_HEAD || true)"
expect "conflict merge parents" 2 "$(git log -1 --format=%P | wc -w | tr -d ' ')"
expect "conflict records the import" "$(git -C "$work/upstream" rev-parse HEAD)" "$(last_import)"

# The workflow's own branch is overwritten by the next run.
git push -q origin "$branch"
reset_repo
expect "rerun over the workflow's branch" conflict "$(pull)"

# A branch that someone else pushed to is left alone.
printf 'package litestream\n\nconst B = 3 // patched\n' > litestream/b.go
git -c user.name=person -c user.email=person@example.com commit -qam "Resolve the conflict"
git push -q --force origin "$branch"
reset_repo
expect "someone else's branch" skipped "$(pull)"
expect "someone else's branch stays on main" main "$(git branch --show-current)"

if [[ "$failures" -ne 0 ]]; then
  echo "$failures failure(s)" >&2
  exit 1
fi
echo "PASS"

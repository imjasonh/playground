#!/usr/bin/env bash
# Tests for publish-nethack-notes.sh. Run:
#   bash .github/scripts/publish-nethack-notes_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
publish="$script_dir/publish-nethack-notes.sh"
failures=0

assert_file() {
  local path="$1"
  local expected="$2"
  local actual
  actual="$(cat "$path")"
  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL: $path" >&2
    echo "  expected: $expected" >&2
    echo "  actual:   $actual" >&2
    failures=$((failures + 1))
  fi
}

assert_eq() {
  local got="$1"
  local want="$2"
  local label="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label" >&2
    echo "  expected: $want" >&2
    echo "  actual:   $got" >&2
    failures=$((failures + 1))
  fi
}

write_notebook() {
  local dir="$1"
  local notes="$2"
  mkdir -p "$dir/nethack-agent/notebook"
  printf '%s\n' "$notes" > "$dir/nethack-agent/notebook/notes.json"
  printf '[]\n' > "$dir/nethack-agent/notebook/procedures.json"
  printf '[]\n' > "$dir/nethack-agent/notebook/endings.json"
}

show_notes() {
  local ref="$1"
  git -C "$work" show "${ref}:nethack-agent/notebook/notes.json"
}

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Keep a real gh, if any, from seeing these calls.
export PATH="$tmp/bin:$PATH"
unset GITHUB_REPOSITORY GITHUB_TOKEN GH_TOKEN || true
mkdir -p "$tmp/bin" "$tmp/gh-state"
cat > "$tmp/bin/gh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
state="${GH_FAKE_STATE:?}"
log="${GH_FAKE_LOG:?}"
printf '%s\n' "$*" >> "$log"
cmd="${1:-}"
sub="${2:-}"
if [[ "$cmd" != "pr" ]]; then
  echo "unexpected gh command: $*" >&2
  exit 1
fi
case "$sub" in
  list)
    if [[ -f "$state/number" ]]; then
      cat "$state/number"
    fi
    ;;
  create)
    if [[ -f "$state/number" ]]; then
      echo "pr already open" >&2
      exit 1
    fi
    printf '42\n' > "$state/number"
    echo "https://example.test/pull/42"
    ;;
  edit)
    printf '%s\n' "$*" > "$state/edit"
    ;;
  close)
    rm -f "$state/number"
    printf '%s\n' "$*" > "$state/close"
    ;;
  *)
    echo "unexpected gh pr command: $*" >&2
    exit 1
    ;;
esac
EOF
chmod +x "$tmp/bin/gh"
export GH_FAKE_STATE="$tmp/gh-state"
export GH_FAKE_LOG="$tmp/gh.log"
: > "$tmp/gh.log"

origin="$tmp/origin.git"
work="$tmp/work"
git init --bare -b main "$origin" >/dev/null
git init -b main "$work" >/dev/null
git -C "$work" config user.name "test"
git -C "$work" config user.email "test@example.com"
write_notebook "$work" '[{"id":"n1","text":"from main"}]'
git -C "$work" add nethack-agent/notebook
git -C "$work" commit -m "main notes" >/dev/null
git -C "$work" remote add origin "$origin"
git -C "$work" push -u origin main >/dev/null

git -C "$work" checkout -b automation/nethack-notes >/dev/null
write_notebook "$work" '[{"id":"n1","text":"from notes branch"}]'
git -C "$work" add nethack-agent/notebook
git -C "$work" commit -m "learned notes" >/dev/null
git -C "$work" push -u origin automation/nethack-notes >/dev/null

git -C "$work" checkout main >/dev/null
write_notebook "$work" '[{"id":"n1","text":"dirty checkout"}]'

(
  cd "$work"
  NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" seed
)
assert_file "$work/nethack-agent/notebook/notes.json" '[{"id":"n1","text":"from notes branch"}]'

# A missing notes branch leaves the checkout notebook alone.
git -C "$work" push origin --delete automation/nethack-notes >/dev/null
git -C "$work" update-ref -d refs/remotes/origin/automation/nethack-notes
write_notebook "$work" '[{"id":"n1","text":"keep checkout"}]'
(
  cd "$work"
  NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" seed
)
assert_file "$work/nethack-agent/notebook/notes.json" '[{"id":"n1","text":"keep checkout"}]'

# Publish writes the notebook onto a branch based on main, and opens a PR.
write_notebook "$work" '[{"id":"n1","text":"from play"}]'
mkdir -p "$work/nethack-agent/results"
printf 'token cost $0.18 list price (9000 tokens, grok-4.6)\n' > "$work/nethack-agent/results/last-run.txt"
(
  cd "$work"
  GH_TOKEN=test \
    NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" publish
)
assert_eq "$(show_notes origin/automation/nethack-notes)" '[{"id":"n1","text":"from play"}]' "published notes"
assert_eq \
  "$(git -C "$work" merge-base origin/automation/nethack-notes origin/main)" \
  "$(git -C "$work" rev-parse origin/main)" \
  "notes branch is based on main"
assert_eq "$(grep -c 'pr create' "$tmp/gh.log" || true)" "1" "opens one pull request"
assert_eq "$(grep -c 'token cost .0.18' "$tmp/gh.log" || true)" "1" "pull request includes the token cost"
assert_file "$tmp/gh-state/number" "42"

# The same notebook does not push again, and still opens a PR if the last
# create never landed.
rm -f "$tmp/gh-state/number"
: > "$tmp/gh.log"
(
  cd "$work"
  GH_TOKEN=test \
    NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" publish
)
assert_eq "$(grep -c 'pr create' "$tmp/gh.log" || true)" "1" "creates the missing pull request"
assert_eq "$(git -C "$work" rev-list --count origin/main..origin/automation/nethack-notes)" "1" "does not add another notes commit"

# A later play updates the existing pull request.
write_notebook "$work" '[{"id":"n1","text":"from second play"}]'
: > "$tmp/gh.log"
(
  cd "$work"
  GH_TOKEN=test \
    NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" publish
)
assert_eq "$(show_notes origin/automation/nethack-notes)" '[{"id":"n1","text":"from second play"}]' "second publish"
assert_eq "$(grep -c 'pr edit' "$tmp/gh.log" || true)" "1" "updates the open pull request"
assert_eq "$(grep -c 'pr create' "$tmp/gh.log" || true)" "0" "does not open a second pull request"

# Notes that match main close the pull request and delete the branch.
write_notebook "$work" '[{"id":"n1","text":"from main"}]'
: > "$tmp/gh.log"
(
  cd "$work"
  GH_TOKEN=test \
    NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" publish
)
if git -C "$work" rev-parse --verify --quiet origin/automation/nethack-notes >/dev/null; then
  echo "FAIL: notes branch still exists after matching main" >&2
  failures=$((failures + 1))
fi
assert_eq "$(grep -c 'pr close' "$tmp/gh.log" || true)" "1" "closes the stale pull request"

# A notes branch that cannot be listed must not fall through to the checkout
# notebook. Publishing that copy would replace newer notes.
broken="$tmp/broken"
git init -b main "$broken" >/dev/null
git -C "$broken" config user.name "test"
git -C "$broken" config user.email "test@example.com"
write_notebook "$broken" '[{"id":"n1","text":"do not publish this"}]'
git -C "$broken" add nethack-agent/notebook
git -C "$broken" commit -m "local notes" >/dev/null
git -C "$broken" remote add origin "$tmp/does-not-exist.git"
set +e
(
  cd "$broken"
  NETHACK_NOTES_BRANCH=automation/nethack-notes \
    NETHACK_NOTES_BASE=main \
    bash "$publish" seed
)
seed_status=$?
set -e
assert_eq "$seed_status" "1" "seed fails when the notes branch cannot be listed"
assert_file "$broken/nethack-agent/notebook/notes.json" '[{"id":"n1","text":"do not publish this"}]'

if [[ "$failures" -ne 0 ]]; then
  echo "$failures assertion(s) failed" >&2
  exit 1
fi
echo "publish-nethack-notes_test.sh: ok"

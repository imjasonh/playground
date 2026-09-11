#!/usr/bin/env bash
# Seed and publish the NetHack learning notebook.
#
# The notebook is not committed onto the feature pull request. A GITHUB_TOKEN
# commit there moves the head SHA and does not start the required checks.
# Play reads and writes automation/nethack-notes instead, so the next run
# sees the notes even before that pull request merges.
set -euo pipefail

BRANCH="${NETHACK_NOTES_BRANCH:-automation/nethack-notes}"
BASE="${NETHACK_NOTES_BASE:-main}"
NOTEBOOK_REL="${NETHACK_NOTEBOOK_REL:-nethack-agent/notebook}"
NOTEBOOK_FILES=(notes.json procedures.json endings.json)
# A play that files a note per turn stays far under this. A larger file is
# not a notebook the next life should load.
MAX_NOTEBOOK_BYTES=1048576

repo_root() {
  git rev-parse --show-toplevel
}

configure_auth() {
  if [[ -z "${GH_TOKEN:-}${GITHUB_TOKEN:-}" ]]; then
    return 0
  fi
  local token="${GH_TOKEN:-${GITHUB_TOKEN}}"
  local repo="${GITHUB_REPOSITORY:-}"
  if [[ -z "$repo" ]]; then
    return 0
  fi
  git remote set-url origin "https://x-access-token:${token}@github.com/${repo}.git"
}

notebook_ref_exists() {
  git rev-parse --verify --quiet "origin/${BRANCH}" >/dev/null
}

copy_json_files() {
  local src="$1"
  local dest="$2"
  local name src_file size
  rm -rf "$dest"
  mkdir -p "$dest"
  for name in "${NOTEBOOK_FILES[@]}"; do
    src_file="$src/$name"
    if [[ -L "$src_file" || ! -f "$src_file" ]]; then
      echo "notebook ${name} must be a regular file" >&2
      return 1
    fi
    size="$(wc -c < "$src_file")"
    if [[ "$size" -gt "$MAX_NOTEBOOK_BYTES" ]]; then
      echo "notebook ${name} is ${size} bytes; limit is ${MAX_NOTEBOOK_BYTES}" >&2
      return 1
    fi
    install -m 0644 -- "$src_file" "$dest/$name"
  done
}

copy_notebook_from_ref() {
  local ref="$1"
  local dest="$2"
  local tmp
  tmp="$(mktemp -d)"
  if ! git archive "$ref" "$NOTEBOOK_REL" | tar -x -C "$tmp"; then
    rm -rf "$tmp"
    return 1
  fi
  if ! copy_json_files "$tmp/$NOTEBOOK_REL" "$dest"; then
    rm -rf "$tmp"
    return 1
  fi
  rm -rf "$tmp"
}

validate_notebook() {
  local dir="$1"
  python3 - "$dir" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
names = ("notes.json", "procedures.json", "endings.json")
counts = []
for name in names:
    path = root / name
    if not path.is_file() or path.is_symlink():
        raise SystemExit(f"missing {path}")
    data = json.loads(path.read_text())
    if not isinstance(data, list):
        raise SystemExit(f"{name} must be a JSON array")
    counts.append(len(data))
print("notes", counts[0], "sequences", counts[1], "endings", counts[2])
PY
}

notebooks_equal() {
  local left="$1"
  local right="$2"
  diff -rq "$left" "$right" >/dev/null 2>&1
}

seed() {
  local root dest listed
  root="$(repo_root)"
  dest="$root/$NOTEBOOK_REL"
  cd "$root"
  configure_auth
  export GIT_TERMINAL_PROMPT=0
  # A failed listing must not fall through to play. Publishing the checkout
  # notebook would replace newer notes on the branch.
  if ! listed="$(git ls-remote --heads origin "refs/heads/${BRANCH}")"; then
    echo "::error::could not list origin/${BRANCH}; refusing to play without the notes branch" >&2
    exit 1
  fi
  if [[ -z "$listed" ]]; then
    echo "No ${BRANCH} ref; keeping the notebook in the checkout."
    return 0
  fi
  git fetch --no-tags origin "$BRANCH"
  if ! copy_notebook_from_ref "origin/${BRANCH}" "$dest"; then
    echo "::error::${BRANCH} has no usable notebook" >&2
    exit 1
  fi
  validate_notebook "$dest" >/dev/null
  echo "Seeded ${NOTEBOOK_REL} from ${BRANCH}."
}

run_report() {
  local path="${NETHACK_RUN_REPORT:-$NOTEBOOK_REL/../results/last-run.txt}"
  local root
  root="$(repo_root)"
  if [[ "$path" != /* ]]; then
    path="$root/$path"
  fi
  if [[ ! -f "$path" ]]; then
    return 0
  fi
  python3 - "$path" <<'PY'
import pathlib, sys
text = pathlib.Path(sys.argv[1]).read_text(errors="replace").replace("\x00", "").strip()
if not text.startswith("token cost "):
    raise SystemExit(0)
print()
print(text[:2000])
PY
}

close_stale() {
  local existing
  existing="$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')"
  if [[ -n "$existing" ]]; then
    gh pr close "$existing" --comment "Notebook matches ${BASE}; closing." || true
  fi
  git push origin --delete "$BRANCH" >/dev/null 2>&1 || true
  git update-ref -d "refs/remotes/origin/${BRANCH}" >/dev/null 2>&1 || true
}

open_or_update_pr() {
  local notebook="$1"
  local pushed="$2"
  local counts title body url existing
  counts="$(validate_notebook "$notebook")"
  local report
  report="$(run_report)"
  title="Update NetHack agent notes"
  body="$(cat <<EOF
Learning notebook from a real \`nethack\` play. The next play reads \`${BRANCH}\` even if this pull request is still open.

${counts}
${report}

Review \`nethack-agent/notebook/\` before merging. This pull request is not set to auto-merge. A failed or fake-screen run does not publish here.

The token that opens this pull request does not start workflows, so required checks may stay pending. The next play does not need this pull request to merge.

Workflow: ${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-local}/actions/runs/${GITHUB_RUN_ID:-local}
EOF
)"
  existing="$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')"
  if [[ -n "$existing" ]]; then
    if [[ "$pushed" -eq 1 ]]; then
      gh pr edit "$existing" --title "$title" --body "$body"
      echo "Updated pull request #${existing}"
    else
      echo "Notes pull request #${existing} already open."
    fi
    return 0
  fi
  url="$(gh pr create --base "$BASE" --head "$BRANCH" --title "$title" --body "$body")"
  echo "Opened ${url}"
}

remove_worktree() {
  local work="$1"
  if [[ -n "$work" ]]; then
    git worktree remove --force "$work" >/dev/null 2>&1 || rm -rf "$work"
  fi
}

push_notebook() {
  local notebook="$1"
  local work head remote_sha
  work="$(mktemp -d)"
  rmdir "$work"
  if ! git worktree add --detach "$work" "origin/${BASE}"; then
    rm -rf "$work"
    return 1
  fi
  if ! copy_json_files "$notebook" "$work/$NOTEBOOK_REL"; then
    remove_worktree "$work"
    return 1
  fi
  git -C "$work" add -- "$NOTEBOOK_REL"
  if git -C "$work" diff --cached --quiet; then
    remove_worktree "$work"
    echo "Notebook matches ${BASE}; not opening a notes pull request."
    close_stale
    return 2
  fi
  git -C "$work" -c user.name="github-actions[bot]" \
    -c user.email="41898282+github-actions[bot]@users.noreply.github.com" \
    commit -m "Update NetHack agent notes from play."
  head="$(git -C "$work" rev-parse HEAD)"
  if notebook_ref_exists; then
    remote_sha="$(git rev-parse "origin/${BRANCH}")"
    if ! git push --force-with-lease="refs/heads/${BRANCH}:${remote_sha}" origin "${head}:refs/heads/${BRANCH}"; then
      remove_worktree "$work"
      return 1
    fi
  elif ! git push origin "${head}:refs/heads/${BRANCH}"; then
    remove_worktree "$work"
    return 1
  fi
  remove_worktree "$work"
  git fetch --no-tags origin "$BRANCH" || true
}

publish() {
  local root staged main_notebook branch_notebook base_sha merge_sha listed
  local need_push=1
  root="$(repo_root)"
  cd "$root"
  if [[ -z "${GH_TOKEN:-}${GITHUB_TOKEN:-}" ]]; then
    echo "::error::GH_TOKEN is required to publish the notebook" >&2
    exit 1
  fi
  if ! command -v gh >/dev/null; then
    echo "::error::gh is required to publish the notebook" >&2
    exit 1
  fi
  export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN}}"
  export GIT_TERMINAL_PROMPT=0
  configure_auth
  staged="$(mktemp -d)"
  if ! copy_json_files "$root/$NOTEBOOK_REL" "$staged/notebook"; then
    echo "::error::notebook is missing required JSON files" >&2
    exit 1
  fi
  validate_notebook "$staged/notebook" >/dev/null

  if ! git fetch --no-tags origin "$BASE"; then
    echo "::error::could not fetch origin/${BASE}" >&2
    exit 1
  fi
  if ! listed="$(git ls-remote --heads origin "refs/heads/${BRANCH}")"; then
    echo "::error::could not list origin/${BRANCH}" >&2
    exit 1
  fi
  if [[ -n "$listed" ]]; then
    git fetch --no-tags origin "$BRANCH"
  fi
  if ! git rev-parse --verify --quiet "origin/${BASE}" >/dev/null; then
    echo "::error::origin/${BASE} is not available" >&2
    exit 1
  fi

  main_notebook="$(mktemp -d)"
  if copy_notebook_from_ref "origin/${BASE}" "$main_notebook/notebook" \
    && notebooks_equal "$staged/notebook" "$main_notebook/notebook"; then
    echo "Notebook matches ${BASE}; not opening a notes pull request."
    close_stale
    return 0
  fi

  if notebook_ref_exists; then
    branch_notebook="$(mktemp -d)"
    if copy_notebook_from_ref "origin/${BRANCH}" "$branch_notebook/notebook" \
      && notebooks_equal "$staged/notebook" "$branch_notebook/notebook"; then
      base_sha="$(git rev-parse "origin/${BASE}")"
      merge_sha="$(git merge-base "origin/${BRANCH}" "origin/${BASE}" || true)"
      if [[ "$merge_sha" == "$base_sha" ]]; then
        need_push=0
      fi
    fi
  fi

  if [[ "$need_push" -eq 1 ]]; then
    local status=0
    push_notebook "$staged/notebook" || status=$?
    if [[ "$status" -eq 2 ]]; then
      return 0
    fi
    if [[ "$status" -ne 0 ]]; then
      return "$status"
    fi
  else
    echo "Notebook already published on ${BRANCH}."
  fi

  open_or_update_pr "$staged/notebook" "$need_push"
}

case "${1:-}" in
  seed) seed ;;
  publish) publish ;;
  *)
    echo "Usage: $0 seed|publish" >&2
    exit 2
    ;;
esac

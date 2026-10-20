#!/usr/bin/env bash
# Pulls upstream Litestream into the litestream/ subtree for the nightly
# update-litestream workflow, and opens, updates, or closes its pull request.
#
#   update-litestream.sh pull
#     Merges upstream into a fresh automation branch. Writes the outputs
#     result (unchanged, merged, conflict, or skipped), upstream, previous,
#     and conflicts.
#   update-litestream.sh open-pr | open-conflict-pr
#     Pushes the branch and opens or updates its pull request. They read
#     UPSTREAM, PREVIOUS, and CONFLICTS from the environment.
#   update-litestream.sh enable-auto-merge <pr-number> | close-stale | report-conflict
set -euo pipefail

BRANCH="${LITESTREAM_UPDATE_BRANCH:-automation/litestream-update}"
BASE="${LITESTREAM_UPDATE_BASE:-main}"
PREFIX="${LITESTREAM_PREFIX:-litestream}"
UPSTREAM_URL="${LITESTREAM_UPSTREAM_URL:-https://github.com/benbjohnson/litestream}"
UPSTREAM_REF="${LITESTREAM_UPSTREAM_REF:-main}"
BOT_NAME="github-actions[bot]"
BOT_EMAIL="41898282+github-actions[bot]@users.noreply.github.com"

_git_identity() {
  git config user.name "$BOT_NAME"
  git config user.email "$BOT_EMAIL"
}

_configure_auth() {
  if [[ -n "${GH_TOKEN:-}" && -n "${GITHUB_REPOSITORY:-}" ]]; then
    git remote set-url origin "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
  fi
}

_output() {
  echo "$1=$2" >> "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
}

# _last_import prints the upstream commit of the most recent subtree import,
# from the git-subtree-split trailer that git subtree writes.
_last_import() {
  local squash
  squash=$(git log --grep="^git-subtree-dir: ${PREFIX}\$" --format=%H -1)
  if [[ -z "$squash" ]]; then
    echo "::error::No git subtree import of ${PREFIX}/ in the history; was it fetched with fetch-depth: 0?" >&2
    exit 1
  fi
  git log -1 --format=%B "$squash" | sed -n 's/^git-subtree-split: //p'
}

_compare_url() {
  echo "${UPSTREAM_URL}/compare/${PREVIOUS:0:12}...${UPSTREAM:0:12}"
}

_push_and_pr() {
  local title="$1" body="$2"
  _configure_auth
  # The lease fails the push if someone pushed after pull checked the branch.
  git push --force-with-lease origin "HEAD:refs/heads/$BRANCH"
  local existing
  existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')
  if [[ -n "$existing" ]]; then
    gh pr edit "$existing" --title "$title" --body "$body"
  else
    gh pr create --base "$BASE" --head "$BRANCH" --title "$title" --body "$body"
    existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number')
  fi
  _output pull-request-number "$existing"
}

case "${1:-}" in
  pull)
    _git_identity
    _configure_auth

    # Don't overwrite a branch that someone else pushed to, for example to
    # resolve conflicts from an earlier run.
    if git fetch --quiet origin "refs/heads/$BRANCH:refs/remotes/origin/$BRANCH" 2>/dev/null; then
      author=$(git log -1 --format=%ae "refs/remotes/origin/$BRANCH")
      if [[ "$author" != "$BOT_EMAIL" ]]; then
        echo "::notice::${BRANCH} has a commit by ${author}; leaving it alone."
        _output result skipped
        exit 0
      fi
    fi

    previous=$(_last_import)
    git fetch --quiet "$UPSTREAM_URL" "$UPSTREAM_REF"
    upstream=$(git rev-parse FETCH_HEAD)
    _output previous "$previous"
    _output upstream "$upstream"
    if [[ "$upstream" == "$previous" ]] || git merge-base --is-ancestor "$upstream" "$previous" 2>/dev/null; then
      echo "${PREFIX}/ is already at upstream ${upstream:0:12}."
      _output result unchanged
      exit 0
    fi

    git checkout -B "$BRANCH"
    message="litestream: pull upstream ${upstream:0:7}"
    if git subtree merge --prefix="$PREFIX" --squash -m "$message" "$upstream"; then
      _output result merged
      exit 0
    fi
    if ! git rev-parse -q --verify MERGE_HEAD > /dev/null; then
      echo "::error::git subtree merge failed without leaving a merge to resolve."
      exit 1
    fi
    # Commit the merge with its conflict markers, so the pull request shows
    # exactly what to resolve. The merge's second parent is the squashed
    # upstream commit, which keeps the subtree history intact.
    conflicts=$(git diff --name-only --diff-filter=U)
    git add -A "$PREFIX"
    git commit --quiet --no-verify --no-edit
    {
      echo "conflicts<<EOF"
      echo "$conflicts"
      echo "EOF"
    } >> "$GITHUB_OUTPUT"
    _output result conflict
    ;;
  open-pr)
    : "${UPSTREAM:?}" "${PREVIOUS:?}"
    _push_and_pr "litestream: pull upstream ${UPSTREAM:0:7}" "$(cat <<EOF
Pulls upstream Litestream into \`litestream/\` with \`git subtree\`:
[\`${PREVIOUS:0:7}...${UPSTREAM:0:7}\`]($(_compare_url)).

The merge was clean. Auto-merge is enabled, so this pull request lands
once the required checks pass. If upstream merged one of the patches in
\`litestream/PATCHES.md\`, delete its row there.

Opened by the [nightly workflow run](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID}).
EOF
)"
    ;;
  open-conflict-pr)
    : "${UPSTREAM:?}" "${PREVIOUS:?}" "${CONFLICTS:?}"
    _push_and_pr "litestream: pull upstream ${UPSTREAM:0:7} (conflicts)" "$(cat <<EOF
Pulls upstream Litestream into \`litestream/\` with \`git subtree\`:
[\`${PREVIOUS:0:7}...${UPSTREAM:0:7}\`]($(_compare_url)).

Upstream's changes conflict with a patch in \`litestream/PATCHES.md\`, in
these files:

$(sed 's/^/- `/; s/$/`/' <<< "$CONFLICTS")

The merge commit contains the conflict markers, so this pull request
doesn't build, and auto-merge is off. To finish the update, check out
\`${BRANCH}\`, resolve the markers, run the tests that
\`litestream/PATCHES.md\` lists, and push. The nightly workflow doesn't
overwrite the branch after someone else pushes to it.

Opened by the [nightly workflow run](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID}).
EOF
)"
    number=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number')
    # A clean update from an earlier night may have enabled auto-merge.
    gh pr merge "$number" --disable-auto 2>/dev/null || true
    ;;
  enable-auto-merge)
    pr_number="${2:-}"
    if [[ -z "$pr_number" ]]; then
      echo "Usage: $0 enable-auto-merge <pr-number>" >&2
      exit 2
    fi
    state=$(gh pr view "$pr_number" --json state --jq .state)
    if [[ "$state" != "OPEN" ]]; then
      echo "PR #$pr_number is $state; skipping auto-merge."
      exit 0
    fi
    # git subtree needs merge commits to find the last import.
    gh pr merge "$pr_number" --auto --merge
    ;;
  close-stale)
    existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')
    if [[ -n "$existing" ]]; then
      gh pr close "$existing" --comment "\`litestream/\` is already at upstream's latest commit; closing." || true
    fi
    _configure_auth
    git push origin --delete "$BRANCH" 2>/dev/null || true
    ;;
  report-conflict)
    echo "::error title=Litestream update has conflicts::Resolve them in the update pull request."
    exit 1
    ;;
  *)
    echo "Usage: $0 pull | open-pr | open-conflict-pr | enable-auto-merge <pr-number> | close-stale | report-conflict" >&2
    exit 2
    ;;
esac

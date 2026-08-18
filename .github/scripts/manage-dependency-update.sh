#!/usr/bin/env bash
# Helpers for the dependency update workflow's publish / report steps.
set -euo pipefail

BRANCH="${DEPENDENCY_UPDATE_BRANCH:-automation/dependency-updates}"
BASE="${DEPENDENCY_UPDATE_BASE:-main}"

_git_identity() {
  git config user.name  "github-actions[bot]"
  git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
}

_stage_dep_paths() {
  # Match the former create-pull-request add-paths globs.
  git add -A -- \
    ':(glob)*/go.mod' \
    ':(glob)*/go.sum' \
    ':(glob)*/package.json' \
    ':(glob)*/package-lock.json' \
    ':(glob)*/vendor/**' \
    ':(glob)*/Cargo.toml' \
    ':(glob)*/Cargo.lock' \
    || true
}

_ensure_branch() {
  # Preserve the working tree (dependency bumps already applied on checkout).
  # Point HEAD at the automation branch name for the upcoming commit/push.
  git checkout -B "$BRANCH"
}

_configure_push_auth() {
  if [[ -z "${GH_TOKEN:-}" ]]; then
    echo "::error::GH_TOKEN is required to push the dependency-update branch" >&2
    exit 1
  fi
  local repo="${GITHUB_REPOSITORY:?}"
  git remote set-url origin "https://x-access-token:${GH_TOKEN}@github.com/${repo}.git"
}

_push_and_pr() {
  local title="$1"
  local body="$2"
  _configure_push_auth
  git push --force-with-lease origin "HEAD:refs/heads/$BRANCH"
  local existing
  existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')
  if [[ -n "$existing" ]]; then
    gh pr edit "$existing" --title "$title" --body "$body"
    echo "pull-request-number=$existing" >> "$GITHUB_OUTPUT"
  else
    local url
    url=$(gh pr create --base "$BASE" --head "$BRANCH" --title "$title" --body "$body")
    local num
    num=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number')
    echo "Opened $url"
    echo "pull-request-number=$num" >> "$GITHUB_OUTPUT"
  fi
}

case "${1:-}" in
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
    # Merge commits match prior dependency-update landings on main.
    # --auto is idempotent when auto-merge is already enabled.
    gh pr merge "$pr_number" --auto --merge
    ;;
  open-success-pr)
    _git_identity
    _ensure_branch
    _stage_dep_paths
    if git diff --cached --quiet; then
      echo "::error::open-success-pr expected staged dependency changes"
      exit 1
    fi
    git commit -m "chore(deps): update dependencies"
    _push_and_pr "chore(deps): update dependencies" "$(cat <<EOF
Automated dependency update. Every upgraded app was built and tested
in the [workflow run](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID}).

Auto-merge is enabled; this PR will merge into \`main\` once required
status checks pass.
EOF
)"
    ;;
  open-failure-pr)
    _git_identity
    _ensure_branch
    _stage_dep_paths
    if git diff --cached --quiet; then
      git commit --allow-empty -m "chore(deps): update dependencies"
    else
      git commit -m "chore(deps): update dependencies"
    fi
    _push_and_pr "chore(deps): update dependencies" "$(cat <<EOF
The daily dependency updater could not safely land these changes.
At least one dependency update, generated-asset refresh, build, or
test step failed.

Review the [workflow run](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID})
before merging.
EOF
)"
    ;;
  close-stale)
    # No dependency changes: close any open automation PR and delete its branch.
    existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')
    if [[ -n "$existing" ]]; then
      gh pr close "$existing" --comment "No dependency changes in this run; closing." || true
    fi
    _configure_push_auth
    git push origin --delete "$BRANCH" 2>/dev/null || true
    ;;
  report-failure)
    echo "::error title=Automatic dependency update failed::Review the failure pull request and workflow summary."
    exit 1
    ;;
  *)
    echo "Usage: $0 enable-auto-merge <pr-number> | open-success-pr | open-failure-pr | close-stale | report-failure" >&2
    exit 2
    ;;
esac

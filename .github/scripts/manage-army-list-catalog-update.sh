#!/usr/bin/env bash
# Publish helpers for the weekly Army List catalog refresh workflow.
set -euo pipefail

BRANCH="${ARMY_LIST_CATALOG_BRANCH:-automation/army-list-catalog}"
BASE="${ARMY_LIST_CATALOG_BASE:-main}"

_git_identity() {
  git config user.name  "github-actions[bot]"
  git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
}

_stage_paths() {
  git add -A -- \
    ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json \
    ios/Tests/PlaygroundTests/Fixtures/ArmyLists \
    || true
}

_ensure_branch() {
  git checkout -B "$BRANCH"
}

_configure_push_auth() {
  if [[ -z "${GH_TOKEN:-}" ]]; then
    echo "::error::GH_TOKEN is required to push the army-list-catalog branch" >&2
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
    gh pr merge "$pr_number" --auto --merge
    ;;
  open-success-pr)
    _git_identity
    _ensure_branch
    _stage_paths
    if git diff --cached --quiet; then
      echo "::error::open-success-pr expected staged catalog changes"
      exit 1
    fi
    version=$(python3 -c 'import json,pathlib; print(json.loads(pathlib.Path("ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json").read_text())["version"])')
    git commit -m "chore(ios): refresh army list catalog to ${version}"
    _push_and_pr "chore(ios): refresh army list catalog to ${version}" "$(cat <<EOF
Weekly refresh of the **bundled** Army List construction catalog from BSData
points + datasheet keyword scrapes.

- Catalog version: \`${version}\`
- Id migrations keep saved lists pointed at the same named datasheets when
  ids would otherwise drift
- Stress fixtures regenerated on macOS by the Swift \`ArmyListValidator\` CLI
  (no second-language rules port)

This catalog stays **in-app / versioned** (no remote fetch). Auto-merge is
enabled; the PR lands on \`main\` once required checks pass.

Workflow: ${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID}
EOF
)"
    ;;
  open-failure-pr)
    _git_identity
    _ensure_branch
    _stage_paths
    if git diff --cached --quiet; then
      git commit --allow-empty -m "chore(ios): army list catalog refresh failed"
    else
      git commit -m "chore(ios): army list catalog refresh (needs review)"
    fi
    _push_and_pr "chore(ios): army list catalog refresh needs review" "$(cat <<EOF
The weekly Army List catalog refresh could not safely auto-merge.
Review the [workflow run](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID})
before merging.
EOF
)"
    ;;
  close-stale)
    existing=$(gh pr list --head "$BRANCH" --base "$BASE" --state open --json number --jq '.[0].number // empty')
    if [[ -n "$existing" ]]; then
      gh pr close "$existing" --comment "No army list catalog changes in this run; closing." || true
    fi
    _configure_push_auth
    git push origin --delete "$BRANCH" 2>/dev/null || true
    ;;
  report-failure)
    echo "::error title=Army list catalog refresh failed::Review the failure pull request and workflow summary."
    exit 1
    ;;
  *)
    echo "Usage: $0 enable-auto-merge <pr-number> | open-success-pr | open-failure-pr | close-stale | report-failure" >&2
    exit 2
    ;;
esac

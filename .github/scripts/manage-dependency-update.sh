#!/usr/bin/env bash
# Helpers for the dependency update workflow's publish / report steps.
set -euo pipefail

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
  report-failure)
    echo "::error title=Automatic dependency update failed::Review the failure pull request and workflow summary."
    exit 1
    ;;
  *)
    echo "Usage: $0 enable-auto-merge <pr-number> | report-failure" >&2
    exit 2
    ;;
esac

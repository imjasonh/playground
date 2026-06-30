#!/usr/bin/env bash
# Commit, publish, or report the result of the dependency update workflow.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

configure_git() {
  git config user.name "github-actions[bot]"
  git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
}

case "${1:-}" in
  push)
    configure_git
    git add -- \
      ':(glob)*/go.mod' \
      ':(glob)*/go.sum' \
      ':(glob)*/package.json' \
      ':(glob)*/package-lock.json' \
      ':(glob)*/vendor/**' \
      ':(glob)*/Cargo.toml' \
      ':(glob)*/Cargo.lock'
    git commit -m "chore(deps): update dependencies"
    git push origin HEAD:main
    ;;
  failure-commit)
    configure_git
    git commit --allow-empty -m "chore(deps): report failed dependency update"
    ;;
  report-failure)
    echo "::error title=Automatic dependency update failed::Review the failure pull request and workflow summary."
    exit 1
    ;;
  *)
    echo "Usage: $0 push | failure-commit | report-failure" >&2
    exit 2
    ;;
esac

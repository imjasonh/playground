#!/usr/bin/env bash
# Discover which exe.dev apps to deploy, for the deploy-exe workflow.
#
# Emits an `apps=<json-array>` line to GITHUB_OUTPUT (and echoes it). Every
# exe app is selected on workflow_dispatch, the first push to a branch, or when
# shared deploy-exe scripts/workflow change; otherwise only the exe apps a
# push changed are selected.
set -euo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# Shared CI for every exe app — a change here should redeploy all of them.
is_shared_exe_path() {
  case "$1" in
    .github/workflows/deploy-exe.yml|\
    .github/scripts/discover-changed-exe.sh|\
    .github/scripts/discover-exe-apps.sh|\
    .github/scripts/mint-exedev-token.sh|\
    .github/scripts/mint-r2-temp-credentials.sh|\
    .github/scripts/ensure-terraform-r2-bucket.sh)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

if [ "${EVENT_NAME:-}" = "workflow_dispatch" ]; then
  echo "Manual dispatch; deploying all exe.dev apps."
  apps=$(bash .github/scripts/discover-exe-apps.sh --all)
elif [ "${BEFORE_SHA:-}" = "0000000000000000000000000000000000000000" ]; then
  echo "No prior commit; deploying all exe.dev apps."
  apps=$(bash .github/scripts/discover-exe-apps.sh --all)
else
  : "${BEFORE_SHA:?BEFORE_SHA must be set for pushes}"
  : "${HEAD_SHA:?HEAD_SHA must be set for pushes}"
  changed=$(git diff --name-only "$BEFORE_SHA" "$HEAD_SHA")
  if [ -z "$changed" ]; then
    apps='[]'
  else
    shared=0
    while IFS= read -r path; do
      if is_shared_exe_path "$path"; then
        shared=1
        break
      fi
    done <<<"$changed"
    if [ "$shared" -eq 1 ]; then
      echo "Shared exe.dev deploy scripts/workflow changed; deploying all exe apps."
      apps=$(bash .github/scripts/discover-exe-apps.sh --all)
    else
      apps=$(printf '%s\n' "$changed" | bash .github/scripts/discover-exe-apps.sh --from-changes)
    fi
  fi
fi

echo "apps=${apps}" >> "$GITHUB_OUTPUT"
echo "exe.dev apps to deploy: ${apps}"

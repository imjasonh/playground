#!/usr/bin/env bash
# List GCP apps to deploy.
#
# An app is a non-hidden top-level directory containing gcp-deploy.json.
# --from-changes selects apps whose watch prefixes intersect the given
# paths. A change to the deploy workflow or its scripts selects every app.
#
# Usage:
#   discover-gcp-apps.sh --all
#   discover-gcp-apps.sh --from-changes [path...]
#
# Prints a JSON array. GCP_DEPLOY_ROOT overrides the repo root.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=SCRIPTDIR/gcp-app.sh
source "$script_dir/gcp-app.sh"

emit_json() {
  if (("$#" == 0)); then
    echo '[]'
    return
  fi
  printf '%s\n' "$@" | sort -u | jq -R . | jq -cs .
}

collect_all() {
  local apps=() app listed
  listed=$(gcp_list_apps)
  while IFS= read -r app; do
    [[ -z "$app" ]] && continue
    # Reject a broken manifest here so --all fails closed.
    gcp_normalize_manifest "$(gcp_repo_root)/$app/gcp-deploy.json" "$app" >/dev/null
    apps+=("$app")
  done <<<"$listed"
  emit_json "${apps[@]+"${apps[@]}"}"
}

collect_from_changes() {
  local paths=("$@") path app
  local deploy_all=0
  local apps=() listed

  for path in "${paths[@]+"${paths[@]}"}"; do
    if gcp_deploy_all_path "$path"; then
      deploy_all=1
    fi
  done
  if ((deploy_all == 1)); then
    collect_all
    return
  fi

  listed=$(gcp_list_apps)
  while IFS= read -r app; do
    [[ -z "$app" ]] && continue
    gcp_normalize_manifest "$(gcp_repo_root)/$app/gcp-deploy.json" "$app" >/dev/null
    if gcp_app_changed "$app" "${paths[@]+"${paths[@]}"}"; then
      apps+=("$app")
    fi
  done <<<"$listed"
  emit_json "${apps[@]+"${apps[@]}"}"
}

mode="${1:---from-changes}"
case "$mode" in
  --all)
    collect_all
    ;;
  --from-changes)
    shift
    if (("$#" == 0)); then
      paths=()
      while IFS= read -r path; do
        paths+=("$path")
      done
      collect_from_changes "${paths[@]+"${paths[@]}"}"
    else
      collect_from_changes "$@"
    fi
    ;;
  *)
    echo "usage: discover-gcp-apps.sh --all | --from-changes [path...]" >&2
    exit 2
    ;;
esac

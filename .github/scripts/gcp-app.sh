#!/usr/bin/env bash
# Shared manifest helpers for GCP Cloud Run deploys.
#
# An app is a top-level directory with gcp-deploy.json. The directory name
# and the Terraform variable "name" must match: the workflow uses the
# GitHub environment gcp-<directory>, and Terraform trusts that name.
#
# Deploy runs terraform apply in <app>/terraform. That module must have a
# GCS backend and the variables project_id and github_repository.
#
# gcp-deploy.json fields:
#   zig     optional bool. When true, CI installs Zig before apply so the
#           ko provider can compile CGO. Default false.
#   watch   optional path prefixes. A push that touches one of them
#           deploys this app. Default is the app directory.
#
# Source this file. Do not execute it.
# shellcheck shell=bash

gcp_repo_root() {
  if [[ -n "${GCP_DEPLOY_ROOT:-}" ]]; then
    (cd "$GCP_DEPLOY_ROOT" && pwd)
    return
  fi
  local here
  here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
  (cd "$here/../.." && pwd)
}

gcp_die() {
  echo "gcp: $*" >&2
  return 1
}

# gcp_match VALUE REGEX LABEL
gcp_match() {
  local value="$1" regex="$2" label="$3"
  if [[ ! "$value" =~ $regex ]]; then
    gcp_die "${label} is invalid: ${value}" || return 1
  fi
}

gcp_require_jq() {
  if ! command -v jq >/dev/null 2>&1; then
    gcp_die "jq is required" || return 1
  fi
}

# Print one app directory name per line.
gcp_list_apps() {
  local root name dir
  root=$(gcp_repo_root)
  for dir in "$root"/*/; do
    [[ -d "$dir" ]] || continue
    name=$(basename "$dir")
    [[ "$name" == .* ]] && continue
    [[ -f "${dir}gcp-deploy.json" ]] || continue
    if [[ ! "$name" =~ ^[a-z0-9][a-z0-9-]*$ ]]; then
      gcp_die "app directory must match [a-z0-9][a-z0-9-]*: ${name}" || return 1
    fi
    echo "$name"
  done
}

# Print canonical JSON for an app manifest.
# gcp_normalize_manifest FILE APP
gcp_normalize_manifest() {
  local file="$1" app="$2"
  local zig watch_json prefix unknown

  gcp_require_jq || return 1
  if [[ ! -f "$file" ]]; then
    gcp_die "manifest not found: ${file}" || return 1
  fi
  if ! jq -e 'type == "object"' "$file" >/dev/null; then
    gcp_die "manifest must be a JSON object: ${file}" || return 1
  fi
  unknown=$(jq -r '[keys[] | select(. != "zig" and . != "watch")] | join(", ")' "$file")
  if [[ -n "$unknown" ]]; then
    gcp_die "unknown manifest fields in ${file}: ${unknown}" || return 1
  fi

  case "$(jq -r 'if .zig == null then "false" elif .zig == true then "true" elif .zig == false then "false" else "invalid" end' "$file")" in
    true) zig=true ;;
    false) zig=false ;;
    *)
      gcp_die "zig must be a boolean in ${file}" || return 1
      ;;
  esac

  if jq -e '.watch == null' "$file" >/dev/null; then
    watch_json=$(jq -n --arg app "$app" '[$app]')
  else
    if ! jq -e '.watch | type == "array" and all(.[]; type == "string")' "$file" >/dev/null; then
      gcp_die "watch must be an array of strings in ${file}" || return 1
    fi
    while IFS= read -r prefix; do
      [[ -z "$prefix" ]] && continue
      gcp_match "$prefix" '^[A-Za-z0-9_][A-Za-z0-9_./-]*$' "watch prefix" || return 1
      if [[ "$prefix" == *..* || "$prefix" == /* ]]; then
        gcp_die "watch prefix must stay inside the repo: ${prefix}" || return 1
      fi
    done < <(jq -r '.watch[]' "$file")
    watch_json=$(jq -c '.watch' "$file")
  fi

  jq -n \
    --argjson zig "$zig" \
    --argjson watch "$watch_json" \
    '{zig: $zig, watch: $watch}'
}

# Print watch prefixes, one per line.
gcp_watch_prefixes() {
  local json
  json=$(gcp_normalize_manifest "$1" "$2") || return 1
  jq -r '.watch[]' <<<"$json"
}

# gcp_app_changed APP PATH...
gcp_app_changed() {
  local app="$1"
  shift
  local root prefix path prefixes
  root=$(gcp_repo_root)
  prefixes=$(gcp_watch_prefixes "$root/$app/gcp-deploy.json" "$app") || return 1
  for path in "$@"; do
    [[ -z "$path" ]] && continue
    while IFS= read -r prefix; do
      [[ -z "$prefix" ]] && continue
      if [[ "$path" == "$prefix" || "$path" == "$prefix"/* ]]; then
        return 0
      fi
    done <<<"$prefixes"
  done
  return 1
}

# True when this path should redeploy every GCP app.
gcp_deploy_all_path() {
  case "$1" in
    .github/workflows/deploy-gcp.yml | \
      .github/scripts/deploy-gcp.sh | \
      .github/scripts/deploy-gcp-result.sh | \
      .github/scripts/gcp-app.sh | \
      .github/scripts/install-zig.sh | \
      .github/scripts/discover-gcp-apps.sh | \
      .github/scripts/discover-changed-gcp.sh)
      return 0
      ;;
  esac
  return 1
}

gcp_valid_project_id() {
  [[ "$1" =~ ^[a-z][a-z0-9-]{4,28}[a-z0-9]$ ]]
}

gcp_valid_bucket() {
  [[ "$1" =~ ^[a-z0-9][a-z0-9._-]{1,61}[a-z0-9]$ ]]
}

gcp_valid_github_repository() {
  [[ "$1" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]
}

gcp_valid_wif_provider() {
  [[ "$1" =~ ^projects/[0-9]+/locations/global/workloadIdentityPools/[a-z][a-z0-9-]{2,30}[a-z0-9]/providers/[a-z][a-z0-9-]{2,30}[a-z0-9]$ ]]
}

gcp_valid_service_account() {
  [[ "$1" =~ ^[a-z][a-z0-9-]{4,28}[a-z0-9]@[a-z][a-z0-9-]{4,28}[a-z0-9]\.iam\.gserviceaccount\.com$ ]]
}

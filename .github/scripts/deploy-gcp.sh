#!/usr/bin/env bash
# Apply one GCP app's Terraform stack.
#
# Auth is already done (google-github-actions/auth). The ko provider in
# the stack builds the image and pushes it with those credentials.
# Terraform then updates the Cloud Run service.
#
# Usage:
#   deploy-gcp.sh --check APP
#   deploy-gcp.sh APP
#
# --check validates the manifest, the identity variables, and that the
# stack has a GCS backend. It does not run terraform.
#
# Env:
#   GCP_PROJECT_ID                  required
#   GCP_WORKLOAD_IDENTITY_PROVIDER  required
#   GCP_DEPLOY_SERVICE_ACCOUNT      required
#   GCP_TF_STATE_BUCKET             required. Same bucket passed to
#                                   terraform init -backend-config.
#   GITHUB_REPOSITORY               required. OWNER/REPO. Actions sets this.
#                                   Passed as github_repository so the
#                                   pool trusts this repo.
#   DRY_RUN=1                       print the terraform commands
#
# Identity variables live on the GitHub environment gcp-<APP>.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=SCRIPTDIR/gcp-app.sh
source "$script_dir/gcp-app.sh"

mode=deploy
if [[ "${1:-}" == "--check" ]]; then
  mode=check
  shift
fi
if (("$#" != 1)); then
  echo "usage: deploy-gcp.sh [--check] APP" >&2
  exit 2
fi
app=$1

if [[ ! "$app" =~ ^[a-z0-9][a-z0-9-]*$ ]]; then
  echo "gcp: app name is invalid: ${app}" >&2
  exit 2
fi

root=$(gcp_repo_root)
manifest="${root}/${app}/gcp-deploy.json"
cfg=$(gcp_normalize_manifest "$manifest" "$app")
zig=$(jq -r '.zig' <<<"$cfg")
tfdir="${root}/${app}/terraform"

missing=()
[[ -n "${GCP_PROJECT_ID:-}" ]] || missing+=("GCP_PROJECT_ID")
[[ -n "${GCP_WORKLOAD_IDENTITY_PROVIDER:-}" ]] || missing+=("GCP_WORKLOAD_IDENTITY_PROVIDER")
[[ -n "${GCP_DEPLOY_SERVICE_ACCOUNT:-}" ]] || missing+=("GCP_DEPLOY_SERVICE_ACCOUNT")
[[ -n "${GCP_TF_STATE_BUCKET:-}" ]] || missing+=("GCP_TF_STATE_BUCKET")
[[ -n "${GITHUB_REPOSITORY:-}" ]] || missing+=("GITHUB_REPOSITORY")
if ((${#missing[@]} > 0)); then
  echo "::error title=GCP deploy is not configured::Missing ${missing[*]}. Set the GCP_* variables on the GitHub environment gcp-${app}. Actions sets GITHUB_REPOSITORY. See cloudrun-sqlite/README.md." >&2
  echo "GitHub environment: gcp-${app}" >&2
  exit 1
fi

if ! gcp_valid_project_id "$GCP_PROJECT_ID"; then
  echo "gcp: GCP_PROJECT_ID is invalid: ${GCP_PROJECT_ID}" >&2
  exit 1
fi
if ! gcp_valid_wif_provider "$GCP_WORKLOAD_IDENTITY_PROVIDER"; then
  echo "gcp: GCP_WORKLOAD_IDENTITY_PROVIDER is invalid" >&2
  exit 1
fi
if ! gcp_valid_service_account "$GCP_DEPLOY_SERVICE_ACCOUNT"; then
  echo "gcp: GCP_DEPLOY_SERVICE_ACCOUNT is invalid: ${GCP_DEPLOY_SERVICE_ACCOUNT}" >&2
  exit 1
fi
if ! gcp_valid_bucket "$GCP_TF_STATE_BUCKET"; then
  echo "gcp: GCP_TF_STATE_BUCKET is invalid: ${GCP_TF_STATE_BUCKET}" >&2
  exit 1
fi
if ! gcp_valid_github_repository "$GITHUB_REPOSITORY"; then
  echo "gcp: GITHUB_REPOSITORY is invalid: ${GITHUB_REPOSITORY}" >&2
  exit 1
fi
if [[ ! -d "$tfdir" ]]; then
  echo "gcp: terraform directory not found: ${tfdir}" >&2
  exit 1
fi
if [[ ! -f "${tfdir}/versions.tf" ]] || ! grep -q 'backend "gcs"' "${tfdir}/versions.tf"; then
  echo "gcp: ${tfdir}/versions.tf must set backend \"gcs\"" >&2
  exit 1
fi
if [[ ! -f "${tfdir}/variables.tf" ]] \
  || ! grep -q 'variable "project_id"' "${tfdir}/variables.tf" \
  || ! grep -q 'variable "github_repository"' "${tfdir}/variables.tf"; then
  echo "gcp: ${tfdir}/variables.tf must declare project_id and github_repository" >&2
  exit 1
fi

cat <<EOF
app: ${app}
environment: gcp-${app}
project: ${GCP_PROJECT_ID}
state bucket: ${GCP_TF_STATE_BUCKET}
github repository: ${GITHUB_REPOSITORY}
deploy service account: ${GCP_DEPLOY_SERVICE_ACCOUNT}
workload identity provider: ${GCP_WORKLOAD_IDENTITY_PROVIDER}
terraform: ${tfdir}
zig: ${zig}
EOF

if [[ "$mode" == "check" ]]; then
  exit 0
fi

run() {
  if [[ "${DRY_RUN:-}" == "1" ]]; then
    printf '+'
    printf ' %q' "$@"
    printf '\n'
    return 0
  fi
  "$@"
}

if [[ "${DRY_RUN:-}" != "1" ]]; then
  command -v terraform >/dev/null 2>&1 || {
    echo "gcp: terraform is not on PATH" >&2
    exit 1
  }
  command -v go >/dev/null 2>&1 || {
    echo "gcp: go is not on PATH" >&2
    exit 1
  }
  if [[ "$zig" == "true" ]]; then
    zig_bin=$(bash "$script_dir/install-zig.sh")
    export PATH="${zig_bin}:${PATH}"
  fi
fi

run terraform -chdir="$tfdir" init \
  -input=false \
  -reconfigure \
  -backend-config="bucket=${GCP_TF_STATE_BUCKET}"

run terraform -chdir="$tfdir" apply \
  -input=false \
  -auto-approve \
  -lock-timeout=5m \
  -var "project_id=${GCP_PROJECT_ID}" \
  -var "github_repository=${GITHUB_REPOSITORY}"

if [[ "${DRY_RUN:-}" == "1" ]]; then
  echo "applied <url>"
  exit 0
fi

url=$(terraform -chdir="$tfdir" output -raw url)
if [[ -z "$url" || "$url" != https://* ]]; then
  echo "gcp: terraform output url is empty or not an https URL" >&2
  exit 1
fi
echo "applied ${url}"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    echo "### ${app}"
    echo
    echo "Applied Terraform. Service: ${url}"
  } >>"$GITHUB_STEP_SUMMARY"
fi

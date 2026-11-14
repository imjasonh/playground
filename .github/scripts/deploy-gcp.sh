#!/usr/bin/env bash
# Apply one GCP app's Terraform stack, or plan it on a pull request.
#
# Auth is already done (google-github-actions/auth). The ko provider
# builds the image and pushes it with those credentials. On main,
# OpenTofu then updates the Cloud Run service. On a pull request,
# tofu plan refreshes state and pushes the image the plan built,
# then this script comments the plan on the pull request. Plan does not
# lock state and does not apply. State records OpenTofu registry
# provider addresses, so this script runs tofu, not terraform.
#
# The plan account can read the state bucket and cannot create objects.
# The GCS backend writes <prefix>/default.tfstate, and a lock beside it,
# the first time it loads a prefix that has no state. A pull request
# cannot do that write. When init fails on that lock, the plan runs
# from a copy of the module with the backend block removed, so OpenTofu
# uses an empty local backend and writes nothing to the state bucket.
# init -backend=false does not work: the next plan still requires the
# gcs backend from the configuration. Apply on main creates the state
# and the resources together.
#
# Usage:
#   deploy-gcp.sh --check APP
#   deploy-gcp.sh --check-plan APP
#   deploy-gcp.sh --plan APP
#   deploy-gcp.sh APP
#
# --check and --check-plan validate the manifest, the identity variables,
# and that the stack has a GCS backend. They do not run tofu.
#
# Env:
#   GCP_PROJECT_ID                  required
#   GCP_TF_STATE_BUCKET             required. Passed to
#                                   tofu init -backend-config.
#   GITHUB_REPOSITORY               required. OWNER/REPO. Actions sets this.
#   GCP_WORKLOAD_IDENTITY_PROVIDER  required for --check and apply
#   GCP_DEPLOY_SERVICE_ACCOUNT      required for --check and apply
#   GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER  required for --check-plan and --plan
#   GCP_PLAN_SERVICE_ACCOUNT        required for --check-plan and --plan
#   PR_NUMBER                       pull request to comment. --plan skips
#                                   the comment when this is empty.
#   GITHUB_TOKEN or GH_TOKEN        token for the comment
#   DRY_RUN=1                       print the tofu commands
#
# Identity variables live on the GitHub environment gcp.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=SCRIPTDIR/gcp-app.sh
source "$script_dir/gcp-app.sh"

mode=deploy
case "${1:-}" in
  --check) mode=check; shift ;;
  --check-plan) mode=plan-check; shift ;;
  --plan) mode=plan; shift ;;
esac
if (("$#" != 1)); then
  echo "usage: deploy-gcp.sh [--check | --check-plan | --plan] APP" >&2
  exit 2
fi
app=$1

if [[ ! "$app" =~ ^[a-z0-9][a-z0-9-]*$ ]]; then
  echo "gcp: app name is invalid: ${app}" >&2
  exit 2
fi

plan_mode=false
if [[ "$mode" == "plan" || "$mode" == "plan-check" ]]; then
  plan_mode=true
fi
if [[ "$plan_mode" == true ]]; then
  identity_provider_name=GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER
  identity_account_name=GCP_PLAN_SERVICE_ACCOUNT
else
  identity_provider_name=GCP_WORKLOAD_IDENTITY_PROVIDER
  identity_account_name=GCP_DEPLOY_SERVICE_ACCOUNT
fi
identity_provider=${!identity_provider_name:-}
identity_account=${!identity_account_name:-}

root=$(gcp_repo_root)
manifest="${root}/${app}/gcp-deploy.json"
cfg=$(gcp_normalize_manifest "$manifest" "$app")
zig=$(jq -r '.zig' <<<"$cfg")
tfdir="${root}/${app}/terraform"

missing=()
[[ -n "${GCP_PROJECT_ID:-}" ]] || missing+=("GCP_PROJECT_ID")
[[ -n "$identity_provider" ]] || missing+=("$identity_provider_name")
[[ -n "$identity_account" ]] || missing+=("$identity_account_name")
[[ -n "${GCP_TF_STATE_BUCKET:-}" ]] || missing+=("GCP_TF_STATE_BUCKET")
[[ -n "${GITHUB_REPOSITORY:-}" ]] || missing+=("GITHUB_REPOSITORY")
if ((${#missing[@]} > 0)); then
  echo "::error title=GCP deploy is not configured::Missing ${missing[*]}. Set the GCP_* variables on the GitHub environment gcp. Actions sets GITHUB_REPOSITORY. See gcp/README.md." >&2
  echo "GitHub environment: gcp" >&2
  exit 1
fi

if ! gcp_valid_project_id "$GCP_PROJECT_ID"; then
  echo "gcp: GCP_PROJECT_ID is invalid: ${GCP_PROJECT_ID}" >&2
  exit 1
fi
if ! gcp_valid_wif_provider "$identity_provider"; then
  echo "gcp: ${identity_provider_name} is invalid" >&2
  exit 1
fi
if ! gcp_valid_service_account "$identity_account"; then
  echo "gcp: ${identity_account_name} is invalid: ${identity_account}" >&2
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
  echo "gcp: OpenTofu directory not found: ${tfdir}" >&2
  exit 1
fi
if [[ ! -f "${tfdir}/versions.tf" ]] || ! grep -q 'backend "gcs"' "${tfdir}/versions.tf"; then
  echo "gcp: ${tfdir}/versions.tf must set backend \"gcs\"" >&2
  exit 1
fi
if [[ ! -f "${tfdir}/variables.tf" ]] \
  || ! grep -q 'variable "project_id"' "${tfdir}/variables.tf"; then
  echo "gcp: ${tfdir}/variables.tf must declare project_id" >&2
  exit 1
fi

if [[ "$plan_mode" == true ]]; then
  account_label="plan service account"
else
  account_label="deploy service account"
fi
cat <<EOF
app: ${app}
environment: gcp
project: ${GCP_PROJECT_ID}
state bucket: ${GCP_TF_STATE_BUCKET}
github repository: ${GITHUB_REPOSITORY}
${account_label}: ${identity_account}
workload identity provider: ${identity_provider}
tofu: ${tfdir}
zig: ${zig}
EOF

if [[ "$mode" == "check" || "$mode" == "plan-check" ]]; then
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
  command -v tofu >/dev/null 2>&1 || {
    echo "gcp: tofu is not on PATH" >&2
    exit 1
  }
  # The ko provider builds Go apps. A stack without Go doesn't need it.
  if [[ -f "${root}/${app}/go.mod" ]]; then
    command -v go >/dev/null 2>&1 || {
      echo "gcp: go is not on PATH" >&2
      exit 1
    }
  fi
  if [[ "$zig" == "true" ]]; then
    # Last line only. install-zig.sh prints the directory and nothing else,
    # and a stray stdout line would land in PATH ahead of zig.
    zig_bin=$(bash "$script_dir/install-zig.sh" | tail -n 1)
    export PATH="${zig_bin}:${PATH}"
    command -v zig >/dev/null 2>&1 || {
      echo "gcp: zig is not on PATH after install (${zig_bin})" >&2
      exit 1
    }
  fi
fi

tf_vars=(
  -var "project_id=${GCP_PROJECT_ID}"
)

gcs_init=(
  tofu -chdir="$tfdir" init
  -input=false
  -reconfigure
  -backend-config="bucket=${GCP_TF_STATE_BUCKET}"
)

# Plan against an empty state when this prefix has never been applied.
# init's GCS backend creates the state object if it is missing, which the
# plan account cannot do. A second pull request cannot create it either:
# the object is not a Terraform resource, and apply runs only on main.
#
# init -backend=false does not stick: the next plan sees backend "gcs" in
# the configuration and refuses to run. Plan from a copy with that block
# removed, so OpenTofu uses an empty local backend and writes nothing to
# the state bucket.
plan_dir=$tfdir
plan_without_state() {
  local log copy
  log=$(mktemp)
  if "${gcs_init[@]}" >"$log" 2>&1; then
    cat "$log"
    rm -f "$log"
    return 0
  fi
  cat "$log" >&2
  if ! grep -q 'default.tflock' "$log" || ! grep -q 'storage.objects.create' "$log"; then
    rm -f "$log"
    return 1
  fi
  rm -f "$log"
  # init saved the GCS backend before the lock write failed. Drop that,
  # or a later command in this directory loads it again.
  rm -rf "${tfdir}/.terraform"
  copy=$(mktemp -d)
  cp "${tfdir}/"*.tf "$copy/"
  python3 - "$copy" <<'PY'
import pathlib, sys

root = pathlib.Path(sys.argv[1])
for path in root.glob("*.tf"):
    text = path.read_text()
    out = []
    i = 0
    while True:
        j = text.find('backend "', i)
        if j < 0:
            out.append(text[i:])
            break
        line_start = text.rfind("\n", 0, j) + 1
        if text[line_start:j].strip() != "":
            out.append(text[i:j + 1])
            i = j + 1
            continue
        brace = text.find("{", j)
        if brace < 0:
            out.append(text[i:])
            break
        depth = 0
        k = brace
        while k < len(text):
            if text[k] == "{":
                depth += 1
            elif text[k] == "}":
                depth -= 1
                if depth == 0:
                    k += 1
                    break
            k += 1
        out.append(text[i:line_start])
        i = k
    path.write_text("".join(out))
PY
  echo "gcp: ${app} has no state yet. Planning against an empty local backend. Nothing is written to ${GCP_TF_STATE_BUCKET}." >&2
  tofu -chdir="$copy" init -input=false
  plan_dir=$copy
}

if [[ "${DRY_RUN:-}" == "1" ]]; then
  run "${gcs_init[@]}"
elif [[ "$plan_mode" == true ]]; then
  plan_without_state
else
  "${gcs_init[@]}"
fi

# Comment the plan on the pull request and on the job summary. The fence
# grows until the plan text cannot close it.
post_plan() {
  local text=$1
  local marker="<!-- gcp-plan:${app} -->"
  local fence='```'
  local max=48000
  local body file existing
  if ((${#text} > max)); then
    text="${text:0:max}"$'\n''...[truncated]'
  fi
  while [[ "$text" == *"$fence"* ]]; do
    fence="${fence}\`"
  done
  # printf does not rescan the plan text, so a $() or backtick in the
  # plan is not executed.
  body=$(printf '%s\n' \
    "$marker" \
    "### ${app} Terraform plan" \
    "" \
    "\`tofu plan -lock=false\` as \`${identity_account}\`. This does not apply." \
    "" \
    "$fence" \
    "$text" \
    "$fence")
  printf '%s\n' "$text"
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    printf '%s\n' "$body" >>"$GITHUB_STEP_SUMMARY"
  fi
  if [[ -z "${PR_NUMBER:-}" ]]; then
    return 0
  fi
  if [[ ! "$PR_NUMBER" =~ ^[0-9]+$ ]]; then
    echo "gcp: PR_NUMBER is invalid: ${PR_NUMBER}" >&2
    exit 1
  fi
  export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
  if [[ -z "${GH_TOKEN}" ]]; then
    echo "gcp: PR_NUMBER is set but no token is available to comment" >&2
    exit 1
  fi
  command -v gh >/dev/null 2>&1 || {
    echo "gcp: gh is not on PATH" >&2
    exit 1
  }
  file=$(mktemp)
  printf '%s\n' "$body" >"$file"
  existing=$(gh api --paginate "repos/${GITHUB_REPOSITORY}/issues/${PR_NUMBER}/comments" \
    --jq ".[] | select(.body | contains(\"${marker}\")) | .id")
  existing=${existing%%$'\n'*}
  if [[ -n "$existing" ]]; then
    gh api --method PATCH "repos/${GITHUB_REPOSITORY}/issues/comments/${existing}" \
      --field "body=@${file}" >/dev/null
  else
    gh api --method POST "repos/${GITHUB_REPOSITORY}/issues/${PR_NUMBER}/comments" \
      --field "body=@${file}" >/dev/null
  fi
  rm -f "$file"
  echo "commented on pull request ${PR_NUMBER}"
}

# The plan comment shows changes. Refresh lines name every resource OpenTofu
# read, which hides the diff.
filter_plan_output() {
  local line started=0
  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      *": Refreshing state..."*|*": Reading..."*|*": Read complete after "*)
        continue
        ;;
    esac
    if [[ "$started" == 0 && -z "$line" ]]; then
      continue
    fi
    started=1
    printf '%s\n' "$line"
  done
}

if [[ "$mode" == "plan" ]]; then
  if [[ "${DRY_RUN:-}" == "1" ]]; then
    run tofu -chdir="$tfdir" plan \
      -input=false \
      -no-color \
      -lock=false \
      "${tf_vars[@]}"
    echo "plan <comment>"
    exit 0
  fi
  plan_text=$(tofu -chdir="$plan_dir" plan \
    -input=false \
    -no-color \
    -lock=false \
    "${tf_vars[@]}" | filter_plan_output)
  if [[ -z "$plan_text" ]]; then
    echo "gcp: tofu plan produced no output" >&2
    exit 1
  fi
  post_plan "$plan_text"
  exit 0
fi

run tofu -chdir="$tfdir" apply \
  -input=false \
  -auto-approve \
  -lock-timeout=5m \
  "${tf_vars[@]}"

if [[ "${DRY_RUN:-}" == "1" ]]; then
  echo "applied <url>"
  exit 0
fi

url=$(tofu -chdir="$tfdir" output -raw url)
if [[ -z "$url" || "$url" != https://* ]]; then
  echo "gcp: tofu output url is empty or not an https URL" >&2
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

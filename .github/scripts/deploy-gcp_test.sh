#!/usr/bin/env bash
# Tests for deploy-gcp.sh. A stub stands in for tofu.
# Run: bash .github/scripts/deploy-gcp_test.sh
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
deploy="$script_dir/deploy-gcp.sh"
repo_root=$(cd "$script_dir/../.." && pwd)

failures=0
fail() {
  echo "FAIL: $*" >&2
  failures=$((failures + 1))
}

assert_eq() {
  local got="$1" want="$2" label="$3"
  if [[ "$got" != "$want" ]]; then
    fail "$label"
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
  fi
}

assert_contains() {
  local haystack="$1" needle="$2" label="$3"
  if [[ "$haystack" != *"$needle"* ]]; then
    fail "$label"
    echo "  missing: $needle" >&2
    echo "  in: $haystack" >&2
  fi
}

project=my-proj-123
bucket=my-proj-123-tfstate
repo=imjasonh/playground
wif='projects/123456789/locations/global/workloadIdentityPools/cloudrun-sqlite-github/providers/github'
sa='cloudrun-sqlite-gha-deploy@my-proj-123.iam.gserviceaccount.com'

check_ok=$(
  GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check cloudrun-sqlite
)
assert_contains "$check_ok" $'environment: gcp\n' "check names the environment"
assert_contains "$check_ok" "state bucket: ${bucket}" "check names the state bucket"
assert_contains "$check_ok" "github repository: ${repo}" "check names the repository"
assert_contains "$check_ok" "zig: true" "cloudrun-sqlite needs zig"

if err=$(GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
  GCP_TF_STATE_BUCKET="$bucket" GITHUB_REPOSITORY="$repo" \
  bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "missing project should fail"
else
  assert_contains "$err" "GCP_PROJECT_ID" "missing project names the variable"
  assert_contains "$err" "GitHub environment: gcp" "missing project names the environment"
fi

if err=$(GCP_PROJECT_ID="$project" GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
  GCP_DEPLOY_SERVICE_ACCOUNT="$sa" GITHUB_REPOSITORY="$repo" \
  bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "missing state bucket should fail"
else
  assert_contains "$err" "GCP_TF_STATE_BUCKET" "missing state bucket names the variable"
fi

if err=$(GCP_PROJECT_ID="$project" GCP_WORKLOAD_IDENTITY_PROVIDER='not-a-provider' \
  GCP_DEPLOY_SERVICE_ACCOUNT="$sa" GCP_TF_STATE_BUCKET="$bucket" \
  GITHUB_REPOSITORY="$repo" bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "bad provider should fail"
else
  assert_contains "$err" "GCP_WORKLOAD_IDENTITY_PROVIDER" "bad provider error"
fi

if err=$(GCP_PROJECT_ID="$project" GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
  GCP_DEPLOY_SERVICE_ACCOUNT='not-an-email' GCP_TF_STATE_BUCKET="$bucket" \
  GITHUB_REPOSITORY="$repo" bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "bad service account should fail"
else
  assert_contains "$err" "GCP_DEPLOY_SERVICE_ACCOUNT" "bad service account error"
fi

if err=$(GCP_PROJECT_ID="$project" GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
  GCP_DEPLOY_SERVICE_ACCOUNT="$sa" GCP_TF_STATE_BUCKET='NOT_A_BUCKET' \
  GITHUB_REPOSITORY="$repo" bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "bad state bucket should fail"
else
  assert_contains "$err" "GCP_TF_STATE_BUCKET" "bad state bucket error"
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/example-app/terraform" "$tmp/bin"
cat >"$tmp/example-app/gcp-deploy.json" <<'EOF'
{
  "zig": true
}
EOF
cat >"$tmp/example-app/terraform/versions.tf" <<'EOF'
terraform {
  backend "gcs" {
    prefix = "example-app"
  }
}
EOF
cat >"$tmp/example-app/terraform/variables.tf" <<'EOF'
variable "project_id" {}
variable "github_repository" {}
variable "state_bucket" {}
EOF

log="$tmp/calls.log"
cat >"$tmp/bin/tofu" <<EOF
#!/bin/sh
printf 'tofu' >> "$log"
printf ' %s' "\$@" >> "$log"
printf '\\n' >> "$log"
if [ "\$2" = "output" ]; then
  if [ -f "$tmp/url.txt" ]; then
    cat "$tmp/url.txt"
  else
    echo "https://example-app-hash-uc.a.run.app"
  fi
fi
if [ "\$2" = "plan" ]; then
  echo 'google_cloud_run_v2_service_iam_member.public[0]: Refreshing state... [id=example]'
  echo 'data.google_iam_workload_identity_pool.github[0]: Reading...'
  echo 'data.google_iam_workload_identity_pool.github[0]: Read complete after 0s [id=pool]'
  echo
  echo "Plan: 0 to add, 0 to change, 0 to destroy."
fi
EOF
cat >"$tmp/bin/go" <<'EOF'
#!/bin/sh
echo go >> "$log"
exit 0
EOF
cat >"$tmp/bin/zig" <<'EOF'
#!/bin/sh
if [ "$1" = "version" ]; then
  echo 0.17.0
fi
EOF
cat >"$tmp/bin/curl" <<EOF
#!/bin/sh
echo curl >> "$log"
exit 99
EOF
cat >"$tmp/bin/gh" <<EOF
#!/bin/sh
printf 'gh' >> "$log"
for arg in "\$@"; do
  printf ' %s' "\$arg" >> "$log"
  case "\$arg" in
    body=@*)
      printf '\\n' >> "$log"
      cat "\${arg#body=@}" >> "$log"
      ;;
  esac
done
printf '\\n' >> "$log"
# A list call prints an existing comment id when GH_COMMENT_ID is set,
# so the script updates that comment instead of posting a second one.
if [ -n "\${GH_COMMENT_ID:-}" ]; then
  case "\$*" in
    *--method*) ;;
    *) printf '%s\n' "\$GH_COMMENT_ID" ;;
  esac
fi
EOF
chmod +x "$tmp/bin/tofu" "$tmp/bin/go" "$tmp/bin/zig" "$tmp/bin/curl" "$tmp/bin/gh"

out=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" example-app
)
calls=$(cat "$log")
assert_contains "$calls" "tofu -chdir=${tmp}/example-app/terraform init -input=false -reconfigure -backend-config=bucket=${bucket}" "tofu init"
assert_contains "$calls" "tofu -chdir=${tmp}/example-app/terraform apply -input=false -auto-approve -lock-timeout=5m -var project_id=${project}" "tofu apply"
assert_contains "$out" "applied https://example-app-hash-uc.a.run.app" "prints the service url"
if [[ "$calls" == *gcloud* || "$calls" == *'ko '* || "$calls" == *curl* || "$calls" == *$'\ngh '* || "$calls" == gh\ * ]]; then
  fail "apply must run tofu, not gcloud, ko, curl, or gh"
  echo "$calls" >&2
fi

# Dry-run prints tofu and does not download Zig.
: >"$log"
dry=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    DRY_RUN=1 \
    bash "$deploy" example-app
)
assert_contains "$dry" "tofu -chdir=${tmp}/example-app/terraform init" "dry-run prints init"
assert_contains "$dry" "applied <url>" "dry-run does not invent a url"
if [[ -s "$log" ]]; then
  fail "dry-run invoked tofu, go, or curl"
  cat "$log" >&2
fi

assert_eq "$(bash "$script_dir/install-zig.sh" --version)" "0.17.0" "zig pin"

: >"$log"
if ! err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$repo_root" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check cloudrun-sqlite 2>&1
); then
  fail "--check failed: $err"
fi
if [[ -s "$log" ]]; then
  fail "--check invoked tofu, go, or curl"
  cat "$log" >&2
fi

# A stack without a GCS backend is refused before apply.
mkdir -p "$tmp/local-app/terraform"
echo '{}' >"$tmp/local-app/gcp-deploy.json"
echo 'terraform {}' >"$tmp/local-app/terraform/versions.tf"
printf 'variable "project_id" {}\nvariable "github_repository" {}\n' >"$tmp/local-app/terraform/variables.tf"
if err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check local-app 2>&1
); then
  fail "local backend should fail"
else
  assert_contains "$err" 'backend "gcs"' "local backend error"
fi

: >"$tmp/url.txt"
if err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" example-app 2>&1
); then
  fail "empty service url should fail"
else
  assert_contains "$err" "tofu output url" "empty service url error"
fi

plan_sa="example-app-gha-plan@${project}.iam.gserviceaccount.com"
plan_wif="projects/123456789/locations/global/workloadIdentityPools/example-app-github/providers/github-plan"

: >"$log"
summary="$tmp/summary.md"
: >"$summary"
plan_out=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER="$plan_wif" \
    GCP_PLAN_SERVICE_ACCOUNT="$plan_sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    GITHUB_STEP_SUMMARY="$summary" \
    PR_NUMBER=12 \
    GH_TOKEN=test-token \
    bash "$deploy" --plan example-app
)
plan_calls=$(cat "$log")
assert_contains "$plan_calls" "tofu -chdir=${tmp}/example-app/terraform plan -input=false -no-color -lock=false -var project_id=${project}" "tofu plan"
assert_contains "$plan_out" "Plan: 0 to add, 0 to change, 0 to destroy." "prints the plan"
if [[ "$plan_out" == *"Refreshing state"* || "$plan_out" == *"Reading..."* || "$(cat "$summary")" == *"Refreshing state"* ]]; then
  fail "plan comment includes refresh lines"
  echo "$plan_out" >&2
fi
assert_contains "$plan_out" "commented on pull request 12" "comments on the pull request"
assert_contains "$(cat "$summary")" "<!-- gcp-plan:example-app -->" "summary has the comment marker"
assert_contains "$(cat "$summary")" "Plan: 0 to add, 0 to change, 0 to destroy." "summary has the plan"
assert_contains "$plan_calls" "repos/${repo}/issues/12/comments" "lists comments before posting"
if grep -E '^tofu .* apply ' <<<"$plan_calls"; then
  fail "plan must not apply"
  echo "$plan_calls" >&2
fi
if [[ "$plan_calls" != *'--method POST'* ]]; then
  fail "plan did not post a new comment"
  echo "$plan_calls" >&2
fi

: >"$log"
update_out=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER="$plan_wif" \
    GCP_PLAN_SERVICE_ACCOUNT="$plan_sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    PR_NUMBER=12 \
    GH_TOKEN=test-token \
    GH_COMMENT_ID=99 \
    bash "$deploy" --plan example-app
)
update_calls=$(cat "$log")
assert_contains "$update_out" "commented on pull request 12" "updates the existing comment"
if [[ "$update_calls" != *'--method PATCH'* || "$update_calls" != *'issues/comments/99'* ]]; then
  fail "plan did not update comment 99"
  echo "$update_calls" >&2
fi
if [[ "$update_calls" == *'--method POST'* ]]; then
  fail "plan posted a second comment"
  echo "$update_calls" >&2
fi

: >"$log"
dry_plan=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER="$plan_wif" \
    GCP_PLAN_SERVICE_ACCOUNT="$plan_sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    PR_NUMBER=12 \
    GH_TOKEN=test-token \
    DRY_RUN=1 \
    bash "$deploy" --plan example-app
)
assert_contains "$dry_plan" "plan -input=false -no-color -lock=false" "dry-run prints plan"
assert_contains "$dry_plan" "plan <comment>" "dry-run does not comment"
if [[ -s "$log" ]]; then
  fail "dry-run plan invoked tofu or gh"
  cat "$log" >&2
fi

if ! err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$repo_root" \
    GCP_PROJECT_ID="$project" \
    GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER="$plan_wif" \
    GCP_PLAN_SERVICE_ACCOUNT="$plan_sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check-plan cloudrun-sqlite 2>&1
); then
  fail "--check-plan failed: $err"
fi

if err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check-plan example-app 2>&1
); then
  fail "missing plan service account should fail"
else
  assert_contains "$err" "GCP_PLAN_SERVICE_ACCOUNT" "missing plan account error"
  assert_contains "$err" "GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER" "missing plan provider error"
fi

# Apply does not require the plan account.
if ! err=$(
  PATH="$tmp/bin:$PATH" \
    GCP_DEPLOY_ROOT="$tmp" \
    GCP_PROJECT_ID="$project" \
    GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" \
    GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
    GCP_TF_STATE_BUCKET="$bucket" \
    GITHUB_REPOSITORY="$repo" \
    bash "$deploy" --check example-app 2>&1
); then
  fail "--check without plan variables failed: $err"
fi

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - deploy-gcp.sh"

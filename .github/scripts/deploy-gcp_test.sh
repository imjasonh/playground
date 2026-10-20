#!/usr/bin/env bash
# Tests for deploy-gcp.sh. A stub stands in for terraform.
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
assert_contains "$check_ok" "environment: gcp-cloudrun-sqlite" "check names the environment"
assert_contains "$check_ok" "state bucket: ${bucket}" "check names the state bucket"
assert_contains "$check_ok" "github repository: ${repo}" "check names the repository"
assert_contains "$check_ok" "zig: true" "cloudrun-sqlite needs zig"

if err=$(GCP_WORKLOAD_IDENTITY_PROVIDER="$wif" GCP_DEPLOY_SERVICE_ACCOUNT="$sa" \
  GCP_TF_STATE_BUCKET="$bucket" GITHUB_REPOSITORY="$repo" \
  bash "$deploy" --check cloudrun-sqlite 2>&1); then
  fail "missing project should fail"
else
  assert_contains "$err" "GCP_PROJECT_ID" "missing project names the variable"
  assert_contains "$err" "gcp-cloudrun-sqlite" "missing project names the environment"
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
EOF

log="$tmp/calls.log"
cat >"$tmp/bin/terraform" <<EOF
#!/bin/sh
printf 'terraform' >> "$log"
printf ' %s' "\$@" >> "$log"
printf '\\n' >> "$log"
if [ "\$2" = "output" ]; then
  if [ -f "$tmp/url.txt" ]; then
    cat "$tmp/url.txt"
  else
    echo "https://example-app-hash-uc.a.run.app"
  fi
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
chmod +x "$tmp/bin/terraform" "$tmp/bin/go" "$tmp/bin/zig" "$tmp/bin/curl"

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
assert_contains "$calls" "terraform -chdir=${tmp}/example-app/terraform init -input=false -reconfigure -backend-config=bucket=${bucket}" "terraform init"
assert_contains "$calls" "terraform -chdir=${tmp}/example-app/terraform apply -input=false -auto-approve -lock-timeout=5m -var project_id=${project} -var github_repository=${repo}" "terraform apply"
assert_contains "$out" "applied https://example-app-hash-uc.a.run.app" "prints the service url"
if [[ "$calls" == *gcloud* || "$calls" == *'ko '* || "$calls" == *curl* ]]; then
  fail "apply must run terraform, not gcloud, ko, or curl"
  echo "$calls" >&2
fi

# Dry-run prints terraform and does not download Zig.
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
assert_contains "$dry" "terraform -chdir=${tmp}/example-app/terraform init" "dry-run prints init"
assert_contains "$dry" "applied <url>" "dry-run does not invent a url"
if [[ -s "$log" ]]; then
  fail "dry-run invoked terraform, go, or curl"
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
  fail "--check invoked terraform, go, or curl"
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
  assert_contains "$err" "terraform output url" "empty service url error"
fi

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - deploy-gcp.sh"

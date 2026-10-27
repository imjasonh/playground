# One deploy account and one plan account for every app in this project.
# deploy-gcp.yml selects the GitHub environment var.github_environment.
# A token for any other environment cannot impersonate these accounts.
#
# The deploy account can change app stacks, including project IAM, and it
# can act as any service account in the project. That is what lets it
# deploy a new app's Cloud Run runtime account without a per-app binding.
# It can already grant itself roles. Pool admin stays with the credentials
# that apply this stack.
#
# The plan account can refresh an app stack and read the state bucket. It
# cannot change Cloud Run, IAM, or objects outside that bucket. ko rebuilds
# the image during plan and pushes it, so the account can push to any
# Artifact Registry repository in the project. It cannot delete images.
#
# The Chrome Web Store account holds no project roles: it exists only so
# chrome-extension.yml can impersonate it over Workload Identity Federation
# and ask IAM to mint it a short-lived OAuth access token scoped to
# https://www.googleapis.com/auth/chromewebstore. That scope is a Chrome
# Web Store grant, not a GCP IAM role, and Google authorizes it only after
# this account's email is linked on the publisher in the Chrome Web Store
# Developer Dashboard (Account > API access). See chrome-extension/README.md.
#
# A pull_request workflow from a fork does not receive an OIDC token.

locals {
  github_deploy_roles = [
    "roles/artifactregistry.admin",
    "roles/browser",
    "roles/iam.roleAdmin",
    "roles/iam.serviceAccountAdmin",
    "roles/iam.serviceAccountUser",
    "roles/iam.workloadIdentityPoolViewer",
    "roles/monitoring.dashboardEditor",
    "roles/resourcemanager.projectIamAdmin",
    "roles/run.admin",
    "roles/serviceusage.serviceUsageAdmin",
    "roles/storage.admin",
  ]

  # Read roles for tofu plan. None of these include object reads, so the
  # plan account cannot read a replica bucket. The state bucket grant
  # below is the only object read, and the image role is the only write.
  github_plan_roles = [
    "roles/artifactregistry.reader",
    "roles/browser",
    "roles/iam.roleViewer",
    "roles/iam.securityReviewer",
    "roles/iam.serviceAccountViewer",
    "roles/iam.workloadIdentityPoolViewer",
    "roles/monitoring.viewer",
    "roles/run.viewer",
    "roles/serviceusage.serviceUsageViewer",
    "roles/storage.bucketViewer",
  ]

  # Push an image during plan. No delete permissions: a pull request
  # must not be able to remove an image Cloud Run is running.
  github_plan_push_permissions = [
    "artifactregistry.files.get",
    "artifactregistry.files.list",
    "artifactregistry.packages.get",
    "artifactregistry.packages.list",
    "artifactregistry.repositories.downloadArtifacts",
    "artifactregistry.repositories.getIamPolicy",
    "artifactregistry.repositories.uploadArtifacts",
    "artifactregistry.tags.create",
    "artifactregistry.tags.get",
    "artifactregistry.tags.list",
    "artifactregistry.tags.update",
    "artifactregistry.versions.get",
    "artifactregistry.versions.list",
  ]
}

resource "google_service_account" "github_deploy" {
  project      = var.project_id
  account_id   = "playground-gha-deploy"
  display_name = "Playground GitHub Actions deploy"
  description  = "Apply any app Terraform stack in this project from GitHub Actions."
}

resource "google_service_account" "github_plan" {
  project      = var.project_id
  account_id   = "playground-gha-plan"
  display_name = "Playground GitHub Actions plan"
  description  = "Run tofu plan for any app stack in this project from a pull request."
}

resource "google_service_account" "github_chromewebstore" {
  project      = var.project_id
  account_id   = "playground-chromewebstore"
  display_name = "Playground Chrome Web Store"
  description  = "Mint a chromewebstore-scoped access token for chrome-extension.yml on main. Link this account's email in the Chrome Web Store Developer Dashboard; GCP project roles do not grant Chrome Web Store access."
}

resource "google_service_account_iam_member" "github_wif" {
  service_account_id = google_service_account.github_deploy.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.deploy_environment/${var.github_environment}"
}

resource "google_service_account_iam_member" "github_plan_wif" {
  service_account_id = google_service_account.github_plan.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.plan_environment/${var.github_environment}"
}

resource "google_service_account_iam_member" "github_chromewebstore_wif" {
  service_account_id = google_service_account.github_chromewebstore.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.chromewebstore_environment/${var.chrome_webstore_github_environment}"
}

resource "google_project_iam_member" "github_deploy" {
  for_each = toset(local.github_deploy_roles)

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${google_service_account.github_deploy.email}"
}

resource "google_project_iam_member" "github_plan" {
  for_each = toset(local.github_plan_roles)

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${google_service_account.github_plan.email}"
}

resource "google_project_iam_custom_role" "github_plan_push" {
  project     = var.project_id
  role_id     = "playground_plan_push"
  title       = "Playground plan image push"
  description = "Push container images while planning an app stack. Cannot delete images."
  permissions = local.github_plan_push_permissions
  stage       = "GA"
}

resource "google_project_iam_member" "github_plan_push" {
  project = var.project_id
  role    = google_project_iam_custom_role.github_plan_push.name
  member  = "serviceAccount:${google_service_account.github_plan.email}"
}

resource "google_storage_bucket_iam_member" "github_plan_state" {
  bucket = var.state_bucket
  role   = "roles/storage.objectViewer"
  member = "serviceAccount:${google_service_account.github_plan.email}"
}

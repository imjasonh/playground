# Service accounts for GitHub Actions. The Workload Identity pool and
# its providers are shared by every app in this project. They live in
# gcp/terraform. Apply that stack before this one.
#
# Leave github_repository empty to skip these accounts.
#
# The shared providers map an attribute the other does not. This stack
# binds each account to the attribute for this app's GitHub environment,
# so a token for another app cannot impersonate these accounts.
#
#   attribute.deploy_environment / gcp-<name>  -> deploy account
#   attribute.plan_environment   / gcp-<name>  -> plan account
#
# The plan account can refresh this stack and read the state bucket. It
# cannot change Cloud Run, IAM, or objects in the replica bucket. ko
# rebuilds the image during plan and pushes it, so the account can also
# push to the image repository. It cannot delete images there.
#
# A pull_request workflow from a fork does not receive an OIDC token, so
# a fork cannot impersonate the plan account.

locals {
  github_environment = var.github_environment != "" ? var.github_environment : "gcp-${var.name}"

  # storage.admin covers the state bucket when that bucket is in this
  # project, and it can read replica objects. projectIamAdmin is how the
  # telemetry bindings are granted. roleAdmin is how the plan push role
  # is created. The deploy account can already grant itself any role.
  # Pool viewer is enough to read the shared pool. Pool admin stays on
  # the credentials that apply gcp/terraform.
  github_deploy_roles = [
    "roles/artifactregistry.admin",
    "roles/browser",
    "roles/iam.roleAdmin",
    "roles/iam.serviceAccountAdmin",
    "roles/iam.workloadIdentityPoolViewer",
    "roles/monitoring.dashboardEditor",
    "roles/resourcemanager.projectIamAdmin",
    "roles/run.admin",
    "roles/serviceusage.serviceUsageAdmin",
    "roles/storage.admin",
  ]

  # Read roles for terraform plan. None of these include object reads,
  # so the plan account cannot read the replica. The state bucket grant
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
  # must not be able to remove the image Cloud Run is running.
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

data "google_iam_workload_identity_pool" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                   = var.project_id
  workload_identity_pool_id = var.workload_identity_pool_id
}

data "google_iam_workload_identity_pool_provider" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                            = var.project_id
  workload_identity_pool_id          = data.google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github"
}

data "google_iam_workload_identity_pool_provider" "github_plan" {
  count = var.github_repository != "" ? 1 : 0

  project                            = var.project_id
  workload_identity_pool_id          = data.google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github-plan"
}

resource "google_service_account" "github_deploy" {
  count = var.github_repository != "" ? 1 : 0

  project      = var.project_id
  account_id   = "${var.name}-gha-deploy"
  display_name = "${var.name} GitHub Actions deploy"
  description  = "Apply the ${var.name} Terraform stack from GitHub Actions."
}

resource "google_service_account" "github_plan" {
  count = var.github_repository != "" ? 1 : 0

  project      = var.project_id
  account_id   = "${var.name}-gha-plan"
  display_name = "${var.name} GitHub Actions plan"
  description  = "Run terraform plan for ${var.name} from a pull request."
}

resource "google_service_account_iam_member" "github_wif" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.github_deploy[0].name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${data.google_iam_workload_identity_pool.github[0].name}/attribute.deploy_environment/${local.github_environment}"
}

resource "google_service_account_iam_member" "github_plan_wif" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.github_plan[0].name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${data.google_iam_workload_identity_pool.github[0].name}/attribute.plan_environment/${local.github_environment}"
}

resource "google_project_iam_member" "github_deploy" {
  for_each = var.github_repository != "" ? toset(local.github_deploy_roles) : toset([])

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

resource "google_project_iam_member" "github_plan" {
  for_each = var.github_repository != "" ? toset(local.github_plan_roles) : toset([])

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${google_service_account.github_plan[0].email}"
}

resource "google_project_iam_custom_role" "github_plan_push" {
  count = var.github_repository != "" ? 1 : 0

  project     = var.project_id
  role_id     = "${replace(var.name, "-", "_")}_plan_push"
  title       = "${var.name} plan image push"
  description = "Push container images while planning ${var.name}. Cannot delete images."
  permissions = local.github_plan_push_permissions
  stage       = "GA"
}

resource "google_artifact_registry_repository_iam_member" "github_plan_push" {
  count = var.github_repository != "" ? 1 : 0

  project    = var.project_id
  location   = google_artifact_registry_repository.images.location
  repository = google_artifact_registry_repository.images.repository_id
  role       = google_project_iam_custom_role.github_plan_push[0].name
  member     = "serviceAccount:${google_service_account.github_plan[0].email}"
}

resource "google_storage_bucket_iam_member" "github_plan_state" {
  count = var.github_repository != "" ? 1 : 0

  bucket = var.state_bucket
  role   = "roles/storage.objectViewer"
  member = "serviceAccount:${google_service_account.github_plan[0].email}"

  lifecycle {
    precondition {
      condition     = var.state_bucket != ""
      error_message = "Set state_bucket to the Terraform state bucket when github_repository is set."
    }
  }
}

resource "google_service_account_iam_member" "github_deploy_runtime" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.service.name
  role               = "roles/iam.serviceAccountUser"
  member             = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

# GitHub Actions applies this stack with Workload Identity Federation.
# Leave github_repository empty to skip these resources.
#
# The pool accepts a token only from .github/workflows/deploy-gcp.yml on
# main, in the GitHub environment gcp-<name>. The deploy account is what
# terraform apply runs as, so it can change the resources in this stack,
# including project IAM. Create it with a local apply before CI uses it.

locals {
  github_environment = var.github_environment != "" ? var.github_environment : "gcp-${var.name}"

  # storage.admin covers the state bucket when that bucket is in this
  # project, and it can read replica objects. projectIamAdmin is how the
  # telemetry bindings are granted.
  github_deploy_roles = [
    "roles/artifactregistry.admin",
    "roles/browser",
    "roles/iam.serviceAccountAdmin",
    "roles/iam.workloadIdentityPoolAdmin",
    "roles/monitoring.dashboardEditor",
    "roles/resourcemanager.projectIamAdmin",
    "roles/run.admin",
    "roles/serviceusage.serviceUsageAdmin",
    "roles/storage.admin",
  ]
}

resource "google_iam_workload_identity_pool" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                   = var.project_id
  workload_identity_pool_id = "${var.name}-github"
  display_name              = "${var.name} GitHub Actions"
  description               = "Federated identity for GitHub Actions deploys of ${var.name}."

  depends_on = [google_project_service.services]
}

resource "google_iam_workload_identity_pool_provider" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github"
  display_name                       = "GitHub"
  description                        = "GitHub OIDC for ${var.github_repository}."

  attribute_mapping = {
    "google.subject"             = "assertion.sub"
    "attribute.actor"            = "assertion.actor"
    "attribute.repository"       = "assertion.repository"
    "attribute.repository_owner" = "assertion.repository_owner"
    "attribute.ref"              = "assertion.ref"
    "attribute.workflow_ref"     = "assertion.workflow_ref"
    "attribute.environment"      = "assertion.environment"
  }

  attribute_condition = join(" && ", [
    "assertion.repository == \"${var.github_repository}\"",
    "assertion.ref == \"refs/heads/main\"",
    "assertion.ref_type == \"branch\"",
    "assertion.workflow_ref == \"${var.github_repository}/${var.github_workflow}@refs/heads/main\"",
    "assertion.environment == \"${local.github_environment}\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_service_account" "github_deploy" {
  count = var.github_repository != "" ? 1 : 0

  project      = var.project_id
  account_id   = "${var.name}-gha-deploy"
  display_name = "${var.name} GitHub Actions deploy"
  description  = "Apply the ${var.name} Terraform stack from GitHub Actions."
}

resource "google_service_account_iam_member" "github_wif" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.github_deploy[0].name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github[0].name}/attribute.repository/${var.github_repository}"
}

resource "google_project_iam_member" "github_deploy" {
  for_each = var.github_repository != "" ? toset(local.github_deploy_roles) : toset([])

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

resource "google_service_account_iam_member" "github_deploy_runtime" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.service.name
  role               = "roles/iam.serviceAccountUser"
  member             = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

# GitHub Actions uses Workload Identity Federation. Leave
# github_repository empty to skip these resources.
#
# Two providers share the pool. Each maps an attribute the other does
# not, and the service account binding uses that attribute. A token from
# one provider cannot impersonate the other account.
#
#   github       refs/heads/main, this workflow, environment gcp-<name>
#                attribute.deploy -> deploy account, which can apply
#   github-plan  a pull request, this workflow, the same environment
#                attribute.plan   -> plan account
#
# The plan provider does not map attribute.repository. The deploy
# binding used to grant that attribute to every token in the pool, so a
# plan token that carried it could apply.
#
# The plan account can refresh this stack and read the state bucket. It
# cannot change Cloud Run, IAM, or objects in the replica bucket. ko
# rebuilds the image during plan and pushes it, so the account can also
# push to the image repository. It cannot delete images there.
#
# A pull_request workflow from a fork does not receive an OIDC token, so
# a fork cannot impersonate the plan account. Apply locally once so both
# accounts exist before CI uses them.

locals {
  github_environment = var.github_environment != "" ? var.github_environment : "gcp-${var.name}"

  # storage.admin covers the state bucket when that bucket is in this
  # project, and it can read replica objects. projectIamAdmin is how the
  # telemetry bindings are granted. roleAdmin is how the plan push role
  # is created. The deploy account can already grant itself any role.
  github_deploy_roles = [
    "roles/artifactregistry.admin",
    "roles/browser",
    "roles/iam.roleAdmin",
    "roles/iam.serviceAccountAdmin",
    "roles/iam.workloadIdentityPoolAdmin",
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

resource "google_iam_workload_identity_pool" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                   = var.project_id
  workload_identity_pool_id = "${var.name}-github"
  display_name              = "${var.name} GitHub Actions"
  description               = "Federated identity for GitHub Actions deploys and plans of ${var.name}."

  depends_on = [google_project_service.services]

  lifecycle {
    precondition {
      condition     = var.state_bucket != ""
      error_message = "Set state_bucket to the Terraform state bucket when github_repository is set."
    }
  }
}

resource "google_iam_workload_identity_pool_provider" "github" {
  count = var.github_repository != "" ? 1 : 0

  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github"
  display_name                       = "GitHub deploy"
  description                        = "GitHub OIDC for apply from main."

  attribute_mapping = {
    "google.subject"             = "assertion.sub"
    "attribute.actor"            = "assertion.actor"
    "attribute.repository"       = "assertion.repository"
    "attribute.repository_owner" = "assertion.repository_owner"
    "attribute.ref"              = "assertion.ref"
    "attribute.workflow_ref"     = "assertion.workflow_ref"
    "attribute.environment"      = "assertion.environment"
    # Only this provider maps attribute.deploy. The plan provider must not.
    "attribute.deploy" = "assertion.repository"
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

resource "google_iam_workload_identity_pool_provider" "github_plan" {
  count = var.github_repository != "" ? 1 : 0

  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github-plan"
  display_name                       = "GitHub plan"
  description                        = "GitHub OIDC for terraform plan on a pull request."

  attribute_mapping = {
    "google.subject"         = "assertion.sub"
    "attribute.actor"        = "assertion.actor"
    "attribute.ref"          = "assertion.ref"
    "attribute.workflow_ref" = "assertion.workflow_ref"
    "attribute.environment"  = "assertion.environment"
    # Only this provider maps attribute.plan. The deploy provider must not.
    # Do not map attribute.repository here. See the file comment.
    "attribute.plan" = "assertion.repository"
  }

  attribute_condition = join(" && ", [
    "assertion.repository == \"${var.github_repository}\"",
    "assertion.event_name == \"pull_request\"",
    "assertion.ref.startsWith(\"refs/pull/\")",
    "assertion.ref_type == \"branch\"",
    "assertion.workflow_ref.startsWith(\"${var.github_repository}/${var.github_workflow}@refs/pull/\")",
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
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github[0].name}/attribute.deploy/${var.github_repository}"
}

resource "google_service_account_iam_member" "github_plan_wif" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.github_plan[0].name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github[0].name}/attribute.plan/${var.github_repository}"
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
}

resource "google_service_account_iam_member" "github_deploy_runtime" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.service.name
  role               = "roles/iam.serviceAccountUser"
  member             = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

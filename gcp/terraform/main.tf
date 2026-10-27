# One GitHub connection for every app in this project.
# iam.tf creates the deploy, plan, and Chrome Web Store accounts and
# binds them to a GitHub environment. An app does not create a pool or
# a GitHub account.
#
# Three providers share the pool. Each maps an attribute the others do
# not. The deploy account is bound to attribute.deploy_environment, the
# plan account to attribute.plan_environment, and the Chrome Web Store
# account to attribute.chromewebstore_environment, so a token minted for
# one cannot impersonate another.
#
#   github              refs/heads/main, deploy-gcp.yml, var.github_environment
#                        attribute.deploy_environment = the environment name
#   github-plan          a pull request, the same workflow, that same environment
#                        attribute.plan_environment   = the environment name
#   github-chromewebstore refs/heads/main, chrome-extension.yml, var.chrome_webstore_github_environment
#                        attribute.chromewebstore_environment = the environment name
#
# A pull_request workflow from a fork does not receive an OIDC token.

resource "google_project_service" "services" {
  for_each = toset([
    "cloudresourcemanager.googleapis.com",
    "iam.googleapis.com",
    "iamcredentials.googleapis.com",
    "sts.googleapis.com",
  ])

  service            = each.key
  disable_on_destroy = false
}

resource "google_iam_workload_identity_pool" "github" {
  project                   = var.project_id
  workload_identity_pool_id = var.pool_id
  display_name              = "GitHub Actions"
  description               = "Federated identity for GitHub Actions. The deploy and plan accounts are in this stack."

  depends_on = [google_project_service.services]
}

resource "google_iam_workload_identity_pool_provider" "github" {
  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github.workload_identity_pool_id
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
    # Only this provider maps attribute.deploy_environment.
    "attribute.deploy_environment" = "assertion.environment"
  }

  attribute_condition = join(" && ", [
    "assertion.repository == \"${var.github_repository}\"",
    "assertion.ref == \"refs/heads/main\"",
    "assertion.ref_type == \"branch\"",
    "assertion.workflow_ref == \"${var.github_repository}/${var.github_workflow}@refs/heads/main\"",
    "assertion.environment == \"${var.github_environment}\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "github_plan" {
  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github.workload_identity_pool_id
  workload_identity_pool_provider_id = "github-plan"
  display_name                       = "GitHub plan"
  description                        = "GitHub OIDC for terraform plan on a pull request."

  attribute_mapping = {
    "google.subject"         = "assertion.sub"
    "attribute.actor"        = "assertion.actor"
    "attribute.ref"          = "assertion.ref"
    "attribute.workflow_ref" = "assertion.workflow_ref"
    "attribute.environment"  = "assertion.environment"
    # Only this provider maps attribute.plan_environment.
    # Do not map attribute.deploy_environment here.
    "attribute.plan_environment" = "assertion.environment"
  }

  attribute_condition = join(" && ", [
    "assertion.repository == \"${var.github_repository}\"",
    "assertion.event_name == \"pull_request\"",
    "assertion.ref.startsWith(\"refs/pull/\")",
    "assertion.ref_type == \"branch\"",
    "assertion.workflow_ref.startsWith(\"${var.github_repository}/${var.github_workflow}@refs/pull/\")",
    "assertion.environment == \"${var.github_environment}\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "github_chromewebstore" {
  project                            = var.project_id
  workload_identity_pool_id          = google_iam_workload_identity_pool.github.workload_identity_pool_id
  workload_identity_pool_provider_id = "github-chromewebstore"
  display_name                       = "GitHub Chrome Web Store"
  description                        = "GitHub OIDC for minting a Chrome Web Store access token from chrome-extension.yml on main. Not a Cloud Run deploy; the bound service account holds no project roles."

  attribute_mapping = {
    "google.subject"             = "assertion.sub"
    "attribute.actor"            = "assertion.actor"
    "attribute.repository"       = "assertion.repository"
    "attribute.repository_owner" = "assertion.repository_owner"
    "attribute.ref"              = "assertion.ref"
    "attribute.workflow_ref"     = "assertion.workflow_ref"
    "attribute.environment"      = "assertion.environment"
    # Only this provider maps attribute.chromewebstore_environment.
    "attribute.chromewebstore_environment" = "assertion.environment"
  }

  attribute_condition = join(" && ", [
    "assertion.repository == \"${var.github_repository}\"",
    "assertion.ref == \"refs/heads/main\"",
    "assertion.ref_type == \"branch\"",
    "assertion.workflow_ref == \"${var.github_repository}/${var.chrome_webstore_github_workflow}@refs/heads/main\"",
    "assertion.environment == \"${var.chrome_webstore_github_environment}\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

# Positive cases: no want markers.

resource "google_iam_workload_identity_pool_provider" "pinned" {
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github"

  attribute_mapping = {
    "google.subject"             = "assertion.sub"
    "attribute.repository"       = "assertion.repository"
    "attribute.repository_owner" = "assertion.repository_owner"
    "attribute.repository_id"    = "assertion.repository_id"
  }

  attribute_condition = join(" && ", [
    "assertion.repository_owner_id == \"9919\"",
    "assertion.repository_id == \"1296269\"",
    "assertion.repository == \"octo-org/octo-repo\"",
    "assertion.ref == \"refs/heads/main\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "id_last" {
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-id-last"

  attribute_mapping = {
    "google.subject" = "assertion.sub"
  }

  attribute_condition = "assertion.ref == \"refs/heads/main\" && \"1296269\" == assertion.repository_id"

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "org_wide_by_id" {
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-org"

  attribute_mapping = {
    "google.subject"          = "assertion.sub"
    "attribute.repository_id" = "assertion.repository_id"
  }

  attribute_condition = "assertion.repository_owner_id == \"9919\""

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

# The condition comes from a local, so the repository check isn't visible
# here. The rules don't guess.
resource "google_iam_workload_identity_pool_provider" "from_local" {
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-local"

  attribute_mapping = {
    "google.subject"         = "assertion.sub"
    "attribute.workflow_ref" = "assertion.workflow_ref"
  }

  attribute_condition = join(" && ", [
    local.github_repository_condition,
    "assertion.ref == \"refs/heads/main\"",
  ])

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

# Not GitHub's issuer.
resource "google_iam_workload_identity_pool_provider" "other_issuer" {
  workload_identity_pool_id          = "partner"
  workload_identity_pool_provider_id = "partner"

  attribute_mapping = {
    "google.subject" = "assertion.sub"
  }

  oidc {
    issuer_uri = "https://idp.example.com"
  }
}

resource "google_service_account_iam_member" "by_repo_id" {
  service_account_id = google_service_account.deploy.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.repository_id/1296269"
}

resource "google_service_account_iam_member" "by_environment" {
  service_account_id = google_service_account.deploy.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.deploy_environment/production"
}

resource "google_iam_workload_identity_pool_provider" "no_condition" { # want "with no attribute_condition"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github"

  attribute_mapping = {
    "google.subject"       = "assertion.sub"
    "attribute.repository" = "assertion.repository"
  }

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "always_true" { # want "empty or always true"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-true"

  attribute_mapping = {
    "google.subject" = "assertion.sub"
  }

  attribute_condition = "true"

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "main_anywhere" { # want "never checks the repository or owner"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-main"

  attribute_mapping = {
    "google.subject"           = "assertion.sub"
    "attribute.repository"     = "assertion.repository"
    "attribute.repository_id"  = "assertion.repository_id"
  }

  attribute_condition = "assertion.ref == \"refs/heads/main\""

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "repo_by_name" { # want "by name"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-name"

  attribute_mapping = {
    "google.subject"       = "assertion.sub"
    "attribute.repository" = "assertion.repository"
  }

  attribute_condition = "assertion.repository == \"octo-org/octo-repo\""

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "owner_by_name" { # want "by name"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-owner"

  attribute_mapping = {
    "google.subject" = "assertion.sub"
  }

  attribute_condition = "assertion.repository_owner == \"octo-org\" && assertion.ref == \"refs/heads/main\""

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "sub_prefix" { # want "by name"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-sub"

  attribute_mapping = {
    "google.subject" = "assertion.sub"
  }

  attribute_condition = "assertion.sub.startsWith(\"repo:octo-org/\")"

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_iam_workload_identity_pool_provider" "mapped_name" { # want "by name"
  workload_identity_pool_id          = "github"
  workload_identity_pool_provider_id = "github-mapped"

  attribute_mapping = {
    "google.subject"       = "assertion.sub"
    "attribute.repository" = "assertion.repository"
  }

  attribute_condition = "attribute.repository in [\"octo-org/a\", \"octo-org/b\"]"

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_service_account_iam_member" "whole_pool" { # want "every identity in the Workload Identity pool"
  service_account_id = google_service_account.deploy.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/*"
}

resource "google_project_iam_member" "whole_pool_literal" { # want "every identity in the Workload Identity pool"
  project = "example-project"
  role    = "roles/storage.objectViewer"
  member  = "principalSet://iam.googleapis.com/projects/123/locations/global/workloadIdentityPools/github/*"
}

resource "google_service_account_iam_member" "repo_name" { # want "binds a GitHub repository or owner by name"
  service_account_id = google_service_account.deploy.name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github.name}/attribute.repository/octo-org/octo-repo"
}

resource "google_service_account_iam_binding" "owner_name" { # want "binds a GitHub repository or owner by name"
  service_account_id = google_service_account.deploy.name
  role               = "roles/iam.workloadIdentityUser"
  members = [
    "principalSet://iam.googleapis.com/projects/123/locations/global/workloadIdentityPools/github/attribute.repository_owner/octo-org",
  ]
}

data "google_iam_policy" "subject" { # want "binds a GitHub repository or owner by name"
  binding {
    role = "roles/iam.workloadIdentityUser"
    members = [
      "principal://iam.googleapis.com/projects/123/locations/global/workloadIdentityPools/github/subject/repo:octo-org/octo-repo:ref:refs/heads/main",
    ]
  }
}

# GitHub Actions Workload Identity Federation scaffolding.
# Leave github_repository empty until you are ready to deploy from GHA.
# Then set it to OWNER/REPO, apply, and wire repo vars/secrets as documented
# in ../README.md ("GitHub Actions CD"). The workflow is
# .github/workflows/deploy-sshapp.yml (skips until those vars exist).
#
#   permissions:
#     id-token: write
#     contents: read
#
#   - uses: google-github-actions/auth@v2
#     with:
#       workload_identity_provider: ${wif_provider}
#       service_account: ${deploy_sa_email}

resource "google_iam_workload_identity_pool" "github" {
  count = var.github_repository != "" ? 1 : 0

  workload_identity_pool_id = "${var.name}-github"
  display_name              = "${var.name} GitHub Actions"
  description               = "Federated identity for GitHub Actions deploys of sshapp."

  depends_on = [google_project_service.services]
}

resource "google_iam_workload_identity_pool_provider" "github" {
  count = var.github_repository != "" ? 1 : 0

  workload_identity_pool_id          = google_iam_workload_identity_pool.github[0].workload_identity_pool_id
  workload_identity_pool_provider_id = "github"
  display_name                       = "GitHub"
  description                        = "GitHub OIDC for ${var.github_repository}."

  attribute_mapping = {
    "google.subject"       = "assertion.sub"
    "attribute.actor"      = "assertion.actor"
    "attribute.repository" = "assertion.repository"
    "attribute.ref"        = "assertion.ref"
  }

  attribute_condition = "assertion.repository == \"${var.github_repository}\""

  oidc {
    issuer_uri = "https://token.actions.githubusercontent.com"
  }
}

resource "google_service_account" "github_deploy" {
  count = var.github_repository != "" ? 1 : 0

  account_id   = "${var.name}-gha-deploy"
  display_name = "${var.name} GitHub Actions deploy"
  description  = "Deploy sshapp images and manifests from GitHub Actions via WIF."
}

resource "google_service_account_iam_member" "github_wif" {
  count = var.github_repository != "" ? 1 : 0

  service_account_id = google_service_account.github_deploy[0].name
  role               = "roles/iam.workloadIdentityUser"
  member             = "principalSet://iam.googleapis.com/${google_iam_workload_identity_pool.github[0].name}/attribute.repository/${var.github_repository}"
}

resource "google_project_iam_member" "github_deploy_roles" {
  for_each = var.github_repository != "" ? toset([
    # Day-2 terraform apply: rebuild ko images, patch Deployments/Services,
    # touch DNS. Bootstrap the cluster locally first; this SA is not meant to
    # create the Autopilot cluster from scratch. Grant the SA objectAdmin (or
    # finer) on the Terraform state bucket separately.
    "roles/artifactregistry.writer",
    "roles/container.developer",
    "roles/dns.admin",
  ]) : toset([])

  project = var.project_id
  role    = each.key
  member  = "serviceAccount:${google_service_account.github_deploy[0].email}"
}

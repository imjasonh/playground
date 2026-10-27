output "workload_identity_pool" {
  description = "Pool resource name. Apps bind service accounts to this pool."
  value       = google_iam_workload_identity_pool.github.name
}

output "workload_identity_provider" {
  description = "Provider resource name for terraform apply from main."
  value       = google_iam_workload_identity_pool_provider.github.name
}

output "plan_workload_identity_provider" {
  description = "Provider resource name for tofu plan on a pull request."
  value       = google_iam_workload_identity_pool_provider.github_plan.name
}

output "github_actions_environment" {
  description = "GitHub environment deploy-gcp.yml selects."
  value       = var.github_environment
}

output "github_actions_service_account" {
  description = "Deploy service account email. This account applies every app stack."
  value       = google_service_account.github_deploy.email
}

output "github_actions_plan_service_account" {
  description = "Plan service account email. This account plans every app stack."
  value       = google_service_account.github_plan.email
}

output "chrome_webstore_workload_identity_provider" {
  description = "Provider resource name for minting a Chrome Web Store access token from chrome-extension.yml on main."
  value       = google_iam_workload_identity_pool_provider.github_chromewebstore.name
}

output "chrome_webstore_github_environment" {
  description = "GitHub environment chrome-extension.yml selects for the publish job."
  value       = var.chrome_webstore_github_environment
}

output "chrome_webstore_service_account" {
  description = "Chrome Web Store service account email. This account holds no project roles; link its email in the Chrome Web Store Developer Dashboard (Account > API access) before use."
  value       = google_service_account.github_chromewebstore.email
}

output "chrome_webstore_github_actions_variables" {
  description = "Variable values for the chrome-webstore GitHub environment, one KEY=VALUE per line."
  value = join("\n", [
    "CHROME_WEBSTORE_WORKLOAD_IDENTITY_PROVIDER=${google_iam_workload_identity_pool_provider.github_chromewebstore.name}",
    "CHROME_WEBSTORE_SERVICE_ACCOUNT=${google_service_account.github_chromewebstore.email}",
  ])
}

output "github_actions_variables" {
  description = "Variable values for the GitHub environment, one KEY=VALUE per line. GCP_TF_STATE_BUCKET is not here; set it to the state bucket name."
  value = join("\n", [
    "GCP_PROJECT_ID=${var.project_id}",
    "GCP_WORKLOAD_IDENTITY_PROVIDER=${google_iam_workload_identity_pool_provider.github.name}",
    "GCP_DEPLOY_SERVICE_ACCOUNT=${google_service_account.github_deploy.email}",
    "GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER=${google_iam_workload_identity_pool_provider.github_plan.name}",
    "GCP_PLAN_SERVICE_ACCOUNT=${google_service_account.github_plan.email}",
  ])
}

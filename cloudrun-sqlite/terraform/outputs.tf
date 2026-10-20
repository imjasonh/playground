output "url" {
  value = google_cloud_run_v2_service.service.uri
}

output "image" {
  value = ko_build.server.image_ref
}

output "replica_url" {
  value = "gs://${google_storage_bucket.replica.name}/db"
}

output "dashboard_url" {
  value = "https://console.cloud.google.com/monitoring/dashboards/custom/${basename(google_monitoring_dashboard.latency.id)}?project=${var.project_id}"
}

output "github_actions_environment" {
  description = "GitHub environment for deploy-gcp.yml. Empty until github_repository is set."
  value       = var.github_repository == "" ? "" : local.github_environment
}

output "github_actions_workload_identity_provider" {
  description = "Workload Identity Provider resource name for google-github-actions/auth. Empty until github_repository is set."
  value       = try(google_iam_workload_identity_pool_provider.github[0].name, "")
}

output "github_actions_service_account" {
  description = "Deploy service account email. Empty until github_repository is set."
  value       = try(google_service_account.github_deploy[0].email, "")
}

output "github_actions_variables" {
  description = "Variable values for the GitHub environment, one KEY=VALUE per line. Empty until github_repository is set."
  value = try(join("\n", [
    "GCP_PROJECT_ID=${var.project_id}",
    "GCP_WORKLOAD_IDENTITY_PROVIDER=${google_iam_workload_identity_pool_provider.github[0].name}",
    "GCP_DEPLOY_SERVICE_ACCOUNT=${google_service_account.github_deploy[0].email}",
  ]), "")
}

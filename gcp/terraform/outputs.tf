output "workload_identity_pool" {
  description = "Pool resource name. Apps bind service accounts to this pool."
  value       = google_iam_workload_identity_pool.github.name
}

output "workload_identity_provider" {
  description = "Provider resource name for terraform apply from main."
  value       = google_iam_workload_identity_pool_provider.github.name
}

output "plan_workload_identity_provider" {
  description = "Provider resource name for terraform plan on a pull request."
  value       = google_iam_workload_identity_pool_provider.github_plan.name
}

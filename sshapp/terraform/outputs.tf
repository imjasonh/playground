output "cluster_name" {
  description = "GKE Autopilot cluster name."
  value       = google_container_cluster.sshapp.name
}

output "cluster_endpoint" {
  description = "GKE control-plane endpoint."
  value       = google_container_cluster.sshapp.endpoint
  sensitive   = true
}

output "artifact_registry_repo" {
  description = "Artifact Registry repository for ko_build images."
  value       = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.apps.repository_id}"
}

output "dns_name_servers" {
  description = "NS records to delegate at your registrar when create_dns_zone is true."
  value       = var.create_dns_zone ? google_dns_managed_zone.apps[0].name_servers : []
}

output "apps" {
  description = "Deployed SSH apps keyed by DNS label."
  value = {
    for name, app in module.app : name => {
      fqdn                        = app.fqdn
      load_balancer_ip            = app.load_balancer_ip
      image_ref                   = app.image_ref
      activator_image_ref         = app.activator_image_ref
      host_key_fingerprint_sha256 = app.host_key_fingerprint_sha256
      scale_to_zero               = app.scale_to_zero
      ssh_command                 = "ssh ${app.fqdn}"
    }
  }
}

output "github_actions_workload_identity_provider" {
  description = "WIF provider resource name for google-github-actions/auth. Empty until github_repository is set."
  value = try(
    google_iam_workload_identity_pool_provider.github[0].name,
    "",
  )
}

output "github_actions_service_account" {
  description = "Deploy service account email for GitHub Actions. Empty until github_repository is set."
  value       = try(google_service_account.github_deploy[0].email, "")
}

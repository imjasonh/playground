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
  description = "NS records to delegate at your registrar when a domain is set and create_dns_zone is true."
  value       = local.create_dns_zone ? google_dns_managed_zone.apps[0].name_servers : []
}

output "mux_load_balancer_ip" {
  description = "Shared mux LoadBalancer IP (ssh.<domain> and *.<domain>)."
  value       = local.mux_load_balancer_ip
}

output "mux_fqdn" {
  description = "Primary SSH hostname for the shared mux. Empty until a domain is set."
  value       = local.manage_dns ? "ssh.${trimsuffix(var.domain, ".")}" : ""
}

# deploy-gcp.sh reports this after apply. SSH, not HTTPS: there is no web
# endpoint. It is the mux hostname when a domain is set, otherwise the
# LoadBalancer IP.
output "url" {
  description = "How to reach the mux over SSH."
  value       = local.manage_dns ? "ssh://ssh.${trimsuffix(var.domain, ".")}" : "ssh://${local.mux_load_balancer_ip}"
}

output "mux_image_ref" {
  description = "ko image reference for the mux."
  value       = ko_build.mux.image_ref
}

output "apps" {
  description = "Deployed SSH apps keyed by mux route name."
  value = {
    for name, app in module.app : name => {
      image_ref     = app.image_ref
      scale_to_zero = app.scale_to_zero
      ssh_command   = "ssh ssh.${trimsuffix(var.domain, ".")} ${name}"
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

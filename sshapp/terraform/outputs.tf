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

output "mux_load_balancer_ip" {
  description = "Shared mux LoadBalancer IP (ssh.<domain> and *.<domain>)."
  value = one([
    for ingress in kubernetes_service_v1.mux.status[0].load_balancer[0].ingress : ingress.ip
    if ingress.ip != null && ingress.ip != ""
  ])
}

output "mux_fqdn" {
  description = "Primary SSH hostname for the shared mux."
  value       = "ssh.${trimsuffix(var.domain, ".")}"
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

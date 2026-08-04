output "gateway_ssh" {
  description = "Public SSH endpoint (user CA / host key live in Secret Manager)"
  value       = "ssh -p 22 join@${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}"
}

output "gateway_ip" {
  value = google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip
}

output "orchestrator_ip" {
  description = "Internal orchestrator IP (VPC only)"
  value       = google_compute_instance.orchestrator.network_interface[0].network_ip
}

output "artifact_registry" {
  value = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.sshcloud.repository_id}"
}

output "images" {
  value = {
    gateway      = ko_build.gateway.image_ref
    orchestrator = ko_build.orchestrator.image_ref
    agent        = ko_build.agent.image_ref
    guestinit    = ko_build.guestinit.image_ref
    fortune      = ko_build.fortune.image_ref
    api          = ko_build.api.image_ref
  }
}

output "fortune_image" {
  description = "Digest-pinned sample app — also auto-deployed to the demo user via local-exec"
  value       = ko_build.fortune.image_ref
}

output "demo_ssh" {
  description = "Demo user (auto-joined + fortune deployed). Private key is in Terraform state."
  value       = "ssh -p 22 -i <demo-key> fortune@${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}"
}

output "demo_private_key_openssh" {
  description = "OpenSSH private key for the bootstrap demo user (sensitive)"
  value       = tls_private_key.demo.private_key_openssh
  sensitive   = true
}

output "snapshots_bucket" {
  value = google_storage_bucket.snapshots.name
}

output "assets_bucket" {
  description = "Upload firecracker and vmlinux here (see README); apps are OCI digests"
  value       = google_storage_bucket.assets.name
}

output "secrets" {
  value = {
    gateway_host_key = google_secret_manager_secret.gateway_host_key.secret_id
    user_ca          = google_secret_manager_secret.user_ca.secret_id
    user_ca_pub      = google_secret_manager_secret.user_ca_pub.secret_id
  }
}

output "agent_mig" {
  value = google_compute_instance_group_manager.agents.name
}

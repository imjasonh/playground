output "gateway_ssh" {
  description = "SSH endpoint (reachable only from ssh_client_cidrs)"
  value       = "ssh -p 22 join@${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}"
}

output "gateway_ip" {
  value = google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip
}

output "gateway_internal_ip" {
  description = "Internal gateway migration-control address"
  value       = google_compute_address.gateway_internal.address
}

output "gateway_known_hosts" {
  description = "Pinned known_hosts entry for the public gateway"
  value = join(" ", [
    google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip,
    split(" ", tls_private_key.gateway_host[tostring(var.gateway_host_key_rotation_epoch)].public_key_openssh)[0],
    split(" ", tls_private_key.gateway_host[tostring(var.gateway_host_key_rotation_epoch)].public_key_openssh)[1],
  ])
}

output "orchestrator_ip" {
  description = "Internal orchestrator IP (VPC only)"
  value       = google_compute_address.orchestrator_internal.address
}

output "snapshot_internal_ip" {
  description = "Internal snapshotd API address"
  value       = google_compute_address.snapshot_internal.address
}

output "artifact_registry" {
  value = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.sshcloud.repository_id}"
}

output "images" {
  value = {
    gateway      = ko_build.gateway.image_ref
    orchestrator = ko_build.orchestrator.image_ref
    agent        = ko_build.agent.image_ref
    snapshot     = ko_build.snapshot.image_ref
    vmmhelper    = ko_build.vmmhelper.image_ref
    taphelper    = ko_build.taphelper.image_ref
    guestinit    = ko_build.guestinit.image_ref
    fortune      = ko_build.fortune.image_ref
  }
}

output "fortune_image" {
  description = "Digest-pinned sample app; optionally deployed when enable_demo_bootstrap=true"
  value       = ko_build.fortune.image_ref
}

output "demo_ssh" {
  description = "Optional demo command; null unless enable_demo_bootstrap=true"
  value = var.enable_demo_bootstrap ? join(" ", [
    "ssh -T -p 22 -i <demo-key>",
    "-o IdentitiesOnly=yes",
    "-o UserKnownHostsFile=<known-hosts>",
    "-o GlobalKnownHostsFile=/dev/null",
    "-o StrictHostKeyChecking=yes",
    "${var.demo_app}@${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip} </dev/null",
  ]) : null
}

output "demo_private_key_openssh" {
  description = "Optional bootstrap user's OpenSSH private key (sensitive, stored in Terraform state)"
  value       = var.enable_demo_bootstrap ? tls_private_key.demo[0].private_key_openssh : null
  sensitive   = true
}

output "snapshots_bucket" {
  value = google_storage_bucket.snapshots.name
}

output "firestore_databases" {
  description = "Separated user/app/quota and placement/operation databases"
  value = {
    user      = google_firestore_database.user.name
    placement = google_firestore_database.placement.name
  }
}

output "snapshot_kms_keys" {
  description = "Separate bucket CMEK and snapshot envelope KEK"
  value = {
    bucket   = google_kms_crypto_key.snapshot_bucket.id
    envelope = google_kms_crypto_key.snapshot_envelope.id
  }
}

output "rotation_status" {
  description = "Non-secret rotation epochs, active control signer, role URIs, and public-key fingerprints"
  value = {
    control_ca_active_slot = var.control_ca_active_slot
    control_ca_epochs      = var.control_ca_rotation_epochs
    control_leaf_epochs    = var.control_leaf_rotation_epochs
    gateway_host_key_epoch = var.gateway_host_key_rotation_epoch
    control_role_uris      = local.control_role_uris
    control_ca_key_fingerprints = {
      for slot, key in local.control_ca_keys : slot => key.public_key_fingerprint_sha256
    }
    control_leaf_key_fingerprints = {
      for role, key in local.control_role_keys : role => key.public_key_fingerprint_sha256
    }
    gateway_host_key_fingerprint = tls_private_key.gateway_host[tostring(var.gateway_host_key_rotation_epoch)].public_key_fingerprint_sha256
    user_ca_key_fingerprint      = tls_private_key.user_ca.public_key_fingerprint_sha256
  }
}

output "assets_bucket" {
  description = "Terraform-managed Firecracker, jailer, and kernel artifacts"
  value       = google_storage_bucket.assets.name
}

output "secrets" {
  value = {
    gateway_host_key = google_secret_manager_secret.gateway_host_key.secret_id
    access_policy    = google_secret_manager_secret.access_policy.secret_id
    user_ca          = google_secret_manager_secret.user_ca.secret_id
    user_ca_pub      = google_secret_manager_secret.user_ca_pub.secret_id
    control_ca_a     = google_secret_manager_secret.control_ca["a"].secret_id
    control_ca_b     = google_secret_manager_secret.control_ca["b"].secret_id
    control_identities = {
      for role, secret in google_secret_manager_secret.control_identity : role => secret.secret_id
    }
  }
}

output "agent_mig" {
  value = google_compute_instance_group_manager.agents.name
}

output "observability" {
  description = "Dedicated log buckets/views, _Default routing gate, and Monitoring dashboard"
  value = {
    platform_log_bucket = google_logging_project_bucket_config.platform.bucket_id
    app_log_bucket      = google_logging_project_bucket_config.app.bucket_id
    platform_log_view   = google_logging_log_view.platform.name
    app_log_view        = google_logging_log_view.app.name
    default_excluded    = var.log_routing_live_verified
    dashboard_id        = google_monitoring_dashboard.sshcloud.id
    billing_budget_id   = try(google_billing_budget.monthly[0].id, null)
  }
}

resource "google_compute_instance_template" "agent" {
  name_prefix  = "${local.prefix}-agent-"
  machine_type = var.agent_machine_type
  tags         = ["${local.prefix}-agent"]
  labels       = local.labels

  disk {
    source_image = data.google_compute_image.debian.self_link
    auto_delete  = true
    boot         = true
    disk_size_gb = var.agent_disk_gb
    disk_type    = "pd-balanced"
  }

  network_interface {
    subnetwork = google_compute_subnetwork.sshcloud.id
  }

  service_account {
    email  = google_service_account.agent.email
    scopes = ["cloud-platform"]
  }

  min_cpu_platform = "Intel Cascade Lake"

  advanced_machine_features {
    enable_nested_virtualization = true
  }

  metadata_startup_script = templatefile("${path.module}/scripts/agent.sh.tftpl", {
    helpers                      = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id                   = var.project_id
    user_ca_pub_secret           = google_secret_manager_secret.user_ca_pub.secret_id
    control_identity_secret      = google_secret_manager_secret.control_identity["agent"].secret_id
    control_ca_current_secret    = google_secret_manager_secret.control_ca[var.control_ca_active_slot].secret_id
    control_ca_previous_secret   = google_secret_manager_secret.control_ca[local.control_standby_slot].secret_id
    project_number               = data.google_project.current.number
    orchestrator_service_account = google_service_account.orchestrator.email
    assets_bucket                = local.asset_bucket
    firecracker_object           = google_storage_bucket_object.firecracker.name
    jailer_object                = google_storage_bucket_object.jailer.name
    kernel_object                = google_storage_bucket_object.kernel.name
    platform_version             = "${google_storage_bucket_object.firecracker.name}:${google_storage_bucket_object.jailer.name}:${google_storage_bucket_object.kernel.name}"
    snapshotd_url                = "https://${google_compute_address.snapshot_internal.address}:8082"
    agent_image                  = ko_build.agent.image_ref
    vmmhelper_image              = ko_build.vmmhelper.image_ref
    taphelper_image              = ko_build.taphelper.image_ref
    guestinit_image              = ko_build.guestinit.image_ref
    rootfs_cache_bytes           = var.agent_rootfs_cache_bytes
  })

  lifecycle {
    create_before_destroy = true
  }

  depends_on = [
    google_secret_manager_secret_version.user_ca_pub,
    google_secret_manager_secret_version.control_identity["agent"],
    google_secret_manager_secret_version.control_ca["a"],
    google_secret_manager_secret_version.control_ca["b"],
    google_secret_manager_secret_iam_member.agent_user_ca_pub,
    google_secret_manager_secret_iam_member.control_identity["agent"],
    google_secret_manager_secret_iam_member.control_ca["agent-a"],
    google_secret_manager_secret_iam_member.control_ca["agent-b"],
    google_storage_bucket_object.firecracker,
    google_storage_bucket_object.jailer,
    google_storage_bucket_object.kernel,
    google_storage_bucket_iam_member.agent_assets,
    google_project_iam_member.observability_writers,
    ko_build.vmmhelper,
    ko_build.taphelper,
    google_artifact_registry_repository_iam_member.pullers["agent"],
    google_compute_router_nat.sshcloud,
    google_compute_instance.snapshot,
  ]
}

resource "google_compute_instance_group_manager" "agents" {
  name               = "${local.prefix}-agents"
  base_instance_name = "${local.prefix}-agent"
  zone               = var.zone
  target_size        = var.agent_count

  version {
    instance_template = google_compute_instance_template.agent.id
  }

  named_port {
    name = "agent"
    port = 8080
  }

  update_policy {
    # Do not destroy stateful hosts just because the template changed. A
    # termination-aware drain controller must exist before proactive rollouts.
    type           = "OPPORTUNISTIC"
    minimal_action = "REPLACE"
  }

}

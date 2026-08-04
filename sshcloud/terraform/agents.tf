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
    helpers            = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id         = var.project_id
    user_ca_pub_secret = google_secret_manager_secret.user_ca_pub.secret_id
    agent_auth_secret  = google_secret_manager_secret.agent_auth.secret_id
    assets_bucket      = local.asset_bucket
    firecracker_object = google_storage_bucket_object.firecracker.name
    kernel_object      = google_storage_bucket_object.kernel.name
    snapshots_bucket   = local.snapshot_bucket
    snapshot_prefix    = local.snapshot_prefix
    agent_image        = ko_build.agent.image_ref
    guestinit_image    = ko_build.guestinit.image_ref
  })

  lifecycle {
    create_before_destroy = true
  }

  depends_on = [
    google_secret_manager_secret_version.user_ca_pub,
    google_secret_manager_secret_version.agent_auth,
    google_secret_manager_secret_iam_member.agent_user_ca_pub,
    google_secret_manager_secret_iam_member.agent_control_auth,
    google_storage_bucket_object.firecracker,
    google_storage_bucket_object.kernel,
    google_storage_bucket.snapshots,
    google_storage_bucket_iam_member.agent_assets,
    google_storage_bucket_iam_member.agent_snapshots,
    google_artifact_registry_repository_iam_member.pullers["agent"],
    google_compute_router_nat.sshcloud,
  ]
}

resource "google_compute_health_check" "agent" {
  name                = "${local.prefix}-agent"
  timeout_sec         = 5
  check_interval_sec  = 10
  healthy_threshold   = 2
  unhealthy_threshold = 3

  http_health_check {
    port         = 8080
    request_path = "/healthz"
  }
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

  auto_healing_policies {
    health_check      = google_compute_health_check.agent.id
    initial_delay_sec = 300
  }
}

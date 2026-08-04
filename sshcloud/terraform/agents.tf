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
    assets_bucket      = local.asset_bucket
    snapshots_bucket   = local.snapshot_bucket
    snapshot_prefix    = local.snapshot_prefix
    agent_image        = ko_build.agent.image_ref
    agent_listen       = local.agent_listen
  })

  lifecycle {
    create_before_destroy = true
  }

  depends_on = [
    google_secret_manager_secret_version.user_ca_pub,
    google_storage_bucket.assets,
    google_storage_bucket.snapshots,
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
    type                  = "PROACTIVE"
    minimal_action        = "REPLACE"
    max_unavailable_fixed = 1
    max_surge_fixed       = 1
  }
}

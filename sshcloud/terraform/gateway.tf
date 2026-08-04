data "google_compute_image" "debian" {
  family  = "debian-12"
  project = "debian-cloud"
}

resource "google_compute_instance" "gateway" {
  name         = "${local.prefix}-gateway"
  machine_type = var.gateway_machine_type
  zone         = var.zone
  tags         = ["${local.prefix}-gateway"]
  labels       = local.labels

  boot_disk {
    initialize_params {
      image = data.google_compute_image.debian.self_link
      size  = var.gateway_disk_gb
      type  = "pd-balanced"
    }
  }

  network_interface {
    subnetwork = google_compute_subnetwork.sshcloud.id
    access_config {} # ephemeral public IP — SSH ingress
  }

  service_account {
    email  = google_service_account.gateway.email
    scopes = ["cloud-platform"]
  }

  metadata_startup_script = templatefile("${path.module}/scripts/gateway.sh.tftpl", {
    helpers         = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    registry_host   = split("/", local.registry)[0]
    project_id      = var.project_id
    host_key_secret = google_secret_manager_secret.gateway_host_key.secret_id
    user_ca_secret  = google_secret_manager_secret.user_ca.secret_id
    gateway_image   = ko_build.gateway.image_ref
    gateway_listen  = local.gateway_listen
    orchestrator_ip = google_compute_instance.orchestrator.network_interface[0].network_ip
  })

  lifecycle {
    replace_triggered_by = [ko_build.gateway]
  }

  depends_on = [
    google_secret_manager_secret_version.gateway_host_key,
    google_secret_manager_secret_version.user_ca,
    google_firestore_database.default,
  ]
}

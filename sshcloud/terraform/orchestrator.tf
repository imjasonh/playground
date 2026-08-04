resource "google_compute_instance" "orchestrator" {
  name         = "${local.prefix}-orchestrator"
  machine_type = var.orchestrator_machine_type
  zone         = var.zone
  tags         = ["${local.prefix}-orchestrator"]
  labels       = local.labels

  boot_disk {
    initialize_params {
      image = data.google_compute_image.debian.self_link
      size  = var.orchestrator_disk_gb
      type  = "pd-balanced"
    }
  }

  network_interface {
    subnetwork = google_compute_subnetwork.sshcloud.id
  }

  service_account {
    email  = google_service_account.orchestrator.email
    scopes = ["cloud-platform"]
  }

  metadata_startup_script = templatefile("${path.module}/scripts/orchestrator.sh.tftpl", {
    helpers            = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id         = var.project_id
    zone               = var.zone
    mig_name           = "${local.prefix}-agents"
    hosts_path         = local.hosts_path
    orchestrator_image = ko_build.orchestrator.image_ref
    orch_listen        = local.orch_listen
  })

  lifecycle {
    replace_triggered_by = [ko_build.orchestrator]
  }

  depends_on = [
    google_firestore_database.default,
    google_compute_instance_group_manager.agents,
  ]
}

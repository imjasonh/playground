resource "google_compute_address" "orchestrator_internal" {
  name         = "${local.prefix}-orchestrator-internal"
  region       = var.region
  address_type = "INTERNAL"
  subnetwork   = google_compute_subnetwork.sshcloud.id
}

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
    network_ip = google_compute_address.orchestrator_internal.address
  }

  service_account {
    email  = google_service_account.orchestrator.email
    scopes = ["cloud-platform"]
  }

  metadata_startup_script = templatefile("${path.module}/scripts/orchestrator.sh.tftpl", {
    helpers             = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id          = var.project_id
    firestore_prefix    = var.firestore_prefix
    firestore_database  = var.firestore_database
    zone                = var.zone
    mig_name            = "${local.prefix}-agents"
    hosts_path          = local.hosts_path
    orchestrator_image  = ko_build.orchestrator.image_ref
    inbound_auth_secret = google_secret_manager_secret.orchestrator_auth.secret_id
    agent_auth_secret   = google_secret_manager_secret.agent_auth.secret_id
    gateway_url         = "http://${google_compute_address.gateway_internal.address}:8079"
  })

  lifecycle {
    replace_triggered_by = [ko_build.orchestrator]
  }

  depends_on = [
    google_firestore_database.sshcloud,
    google_compute_instance_group_manager.agents,
    google_secret_manager_secret_version.orchestrator_auth,
    google_secret_manager_secret_version.agent_auth,
    google_secret_manager_secret_iam_member.orchestrator_inbound_auth,
    google_secret_manager_secret_iam_member.orchestrator_agent_auth,
    google_artifact_registry_repository_iam_member.pullers["orchestrator"],
    google_project_iam_member.orchestrator_compute_viewer,
    google_project_iam_member.orchestrator_datastore,
    google_compute_router_nat.sshcloud,
  ]
}

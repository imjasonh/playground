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
    helpers                      = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id                   = var.project_id
    firestore_prefix             = var.firestore_prefix
    user_firestore_database      = var.user_firestore_database
    placement_firestore_database = var.placement_firestore_database
    zone                         = var.zone
    mig_name                     = "${local.prefix}-agents"
    hosts_path                   = local.hosts_path
    orchestrator_image           = ko_build.orchestrator.image_ref
    control_identity_secret      = google_secret_manager_secret.control_identity["orchestrator"].secret_id
    # The runtime trusts both fixed slots. Signing-slot changes reissue leaves
    # without changing this startup script or replacing the instance.
    control_ca_current_secret    = google_secret_manager_secret.control_ca["a"].secret_id
    control_ca_previous_secret   = google_secret_manager_secret.control_ca["b"].secret_id
    gateway_url                  = "https://${google_compute_address.gateway_internal.address}:8079"
    project_number               = data.google_project.current.number
    gateway_service_account      = google_service_account.gateway.email
    orchestrator_service_account = google_service_account.orchestrator.email
    agent_service_account        = google_service_account.agent.email
    drain_script_b64             = filebase64("${path.module}/../hack/drain-agent-host.sh")
  })

  lifecycle {
    replace_triggered_by = [ko_build.orchestrator]
  }

  depends_on = [
    google_firestore_database.user,
    google_firestore_database.placement,
    google_compute_instance_group_manager.agents,
    google_secret_manager_secret_version.control_identity["orchestrator"],
    google_secret_manager_secret_version.control_ca["a"],
    google_secret_manager_secret_version.control_ca["b"],
    google_secret_manager_secret_iam_member.control_identity["orchestrator"],
    google_secret_manager_secret_iam_member.control_ca["orchestrator-a"],
    google_secret_manager_secret_iam_member.control_ca["orchestrator-b"],
    google_artifact_registry_repository_iam_member.pullers["orchestrator"],
    google_project_iam_member.orchestrator_compute_viewer,
    google_project_iam_member.orchestrator_user_datastore,
    google_project_iam_member.orchestrator_placement_datastore,
    google_project_iam_member.observability_writers,
    google_compute_router_nat.sshcloud,
  ]
}

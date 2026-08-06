resource "google_compute_address" "snapshot_internal" {
  name         = "${local.prefix}-snapshot-internal"
  region       = var.region
  address_type = "INTERNAL"
  subnetwork   = google_compute_subnetwork.sshcloud.id
}

resource "google_compute_instance" "snapshot" {
  name         = "${local.prefix}-snapshot"
  machine_type = var.snapshot_machine_type
  zone         = var.zone
  tags         = ["${local.prefix}-snapshot"]
  labels       = local.labels

  boot_disk {
    initialize_params {
      image = data.google_compute_image.debian.self_link
      size  = var.snapshot_disk_gb
      type  = "pd-balanced"
    }
  }

  network_interface {
    subnetwork = google_compute_subnetwork.sshcloud.id
    network_ip = google_compute_address.snapshot_internal.address
  }

  service_account {
    email  = google_service_account.snapshot.email
    scopes = ["cloud-platform"]
  }

  metadata_startup_script = templatefile("${path.module}/scripts/snapshotd.sh.tftpl", {
    helpers                      = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    project_id                   = var.project_id
    project_number               = data.google_project.current.number
    firestore_prefix             = var.firestore_prefix
    placement_firestore_database = var.placement_firestore_database
    staging_max_bytes            = var.snapshot_staging_max_bytes
    staging_max_operations       = var.snapshot_staging_max_operations
    staging_max_per_agent        = var.snapshot_staging_max_per_agent
    snapshot_image               = ko_build.snapshot.image_ref
    snapshots_bucket             = local.snapshot_bucket
    snapshot_prefix              = local.snapshot_prefix
    kms_key                      = google_kms_crypto_key.snapshot_envelope.id
    agent_service_account        = google_service_account.agent.email
    control_identity_secret      = google_secret_manager_secret.control_identity["snapshot"].secret_id
    # Both fixed trust slots reload independently of the active leaf issuer.
    control_ca_current_secret  = google_secret_manager_secret.control_ca["a"].secret_id
    control_ca_previous_secret = google_secret_manager_secret.control_ca["b"].secret_id
  })

  lifecycle {
    replace_triggered_by = [ko_build.snapshot]
  }

  depends_on = [
    google_firestore_database.placement,
    google_secret_manager_secret_version.control_identity["snapshot"],
    google_secret_manager_secret_version.control_ca["a"],
    google_secret_manager_secret_version.control_ca["b"],
    google_secret_manager_secret_iam_member.control_identity["snapshot"],
    google_secret_manager_secret_iam_member.control_ca["snapshot-a"],
    google_secret_manager_secret_iam_member.control_ca["snapshot-b"],
    google_artifact_registry_repository_iam_member.pullers["snapshot"],
    google_project_iam_member.snapshot_datastore,
    google_storage_bucket_iam_member.snapshot_objects,
    google_kms_crypto_key_iam_member.snapshot_kek,
    google_project_iam_member.observability_writers,
    google_compute_router_nat.sshcloud,
  ]
}

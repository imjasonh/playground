data "google_compute_image" "debian" {
  family  = "debian-12"
  project = "debian-cloud"

  depends_on = [module.project_services]
}

resource "google_compute_address" "gateway" {
  name       = "${local.prefix}-gateway"
  region     = var.region
  depends_on = [module.project_services]
}

resource "google_compute_address" "gateway_internal" {
  name         = "${local.prefix}-gateway-internal"
  region       = var.region
  address_type = "INTERNAL"
  subnetwork   = google_compute_subnetwork.sshcloud.id
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
    network_ip = google_compute_address.gateway_internal.address
    access_config {
      nat_ip = google_compute_address.gateway.address
    }
  }

  service_account {
    email  = google_service_account.gateway.email
    scopes = ["cloud-platform"]
  }

  metadata_startup_script = templatefile("${path.module}/scripts/gateway.sh.tftpl", {
    helpers              = templatefile("${path.module}/scripts/run-container.sh.tftpl", { registry_host = split("/", local.registry)[0], project_id = var.project_id })
    registry_host        = split("/", local.registry)[0]
    project_id           = var.project_id
    firestore_prefix     = var.firestore_prefix
    firestore_database   = var.firestore_database
    host_key_secret      = google_secret_manager_secret.gateway_host_key.secret_id
    user_ca_secret       = google_secret_manager_secret.user_ca.secret_id
    control_auth_secret  = google_secret_manager_secret.orchestrator_auth.secret_id
    access_policy_secret = google_secret_manager_secret.access_policy.secret_id
    gateway_image        = ko_build.gateway.image_ref
    gateway_listen       = local.gateway_listen
    control_listen       = "${google_compute_address.gateway_internal.address}:8079"
    orchestrator_ip      = google_compute_address.orchestrator_internal.address
  })

  lifecycle {
    replace_triggered_by = [ko_build.gateway]
  }

  depends_on = [
    google_secret_manager_secret_version.gateway_host_key,
    google_secret_manager_secret_version.user_ca,
    google_secret_manager_secret_version.orchestrator_auth,
    google_secret_manager_secret_version.access_policy,
    google_secret_manager_secret_iam_member.gateway_host_key,
    google_secret_manager_secret_iam_member.gateway_user_ca,
    google_secret_manager_secret_iam_member.gateway_orchestrator_auth,
    google_secret_manager_secret_iam_member.gateway_access_policy,
    google_firestore_database.sshcloud,
    google_project_iam_member.gateway_datastore,
    google_artifact_registry_repository_iam_member.pullers["gateway"],
  ]
}

provider "google" {
  project = var.project_id
  region  = var.region
  zone    = var.zone
}

provider "ko" {
  repo = "${var.region}-docker.pkg.dev/${var.project_id}/${var.name_prefix}"
}

locals {
  prefix = var.name_prefix
  labels = {
    app     = "sshcloud"
    managed = "terraform"
  }
  asset_bucket    = google_storage_bucket.assets.name
  snapshot_bucket = google_storage_bucket.snapshots.name
  snapshot_prefix = "sshcloud/snaps"
  hosts_path      = "/var/lib/sshcloud/hosts"
  gateway_listen  = "0.0.0.0:22"
  registry        = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.sshcloud.repository_id}"
}

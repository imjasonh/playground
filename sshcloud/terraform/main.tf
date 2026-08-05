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
  services = toset([
    "compute.googleapis.com",
    "firestore.googleapis.com",
    "secretmanager.googleapis.com",
    "artifactregistry.googleapis.com",
    "iam.googleapis.com",
    "iamcredentials.googleapis.com",
    "storage.googleapis.com",
    "serviceusage.googleapis.com",
    "cloudresourcemanager.googleapis.com",
    "iap.googleapis.com",
  ])
  asset_bucket    = google_storage_bucket.assets.name
  snapshot_bucket = google_storage_bucket.snapshots.name
  snapshot_prefix = "sshcloud/snaps"
  hosts_path      = "/var/lib/sshcloud/hosts"
  gateway_listen  = "0.0.0.0:22"
  registry        = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.sshcloud.repository_id}"
}

resource "google_project_service" "services" {
  for_each                   = local.services
  project                    = var.project_id
  service                    = each.value
  disable_on_destroy         = false
  disable_dependent_services = false
}

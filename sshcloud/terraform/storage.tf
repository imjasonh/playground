resource "google_storage_bucket" "snapshots" {
  name                        = "${local.prefix}-${var.project_id}-snaps"
  location                    = var.region
  uniform_bucket_level_access = true
  public_access_prevention    = "enforced"
  force_destroy               = false
  labels                      = local.labels
  default_kms_key_name        = google_kms_crypto_key.snapshot_bucket.id

  versioning {
    enabled = true
  }

  depends_on = [
    module.project_services,
    google_kms_crypto_key_iam_member.snapshot_bucket_cmek,
  ]
}

resource "google_storage_bucket" "assets" {
  name                        = "${local.prefix}-${var.project_id}-assets"
  location                    = var.region
  uniform_bucket_level_access = true
  public_access_prevention    = "enforced"
  force_destroy               = false
  labels                      = local.labels

  depends_on = [module.project_services]
}

resource "google_storage_bucket_object" "firecracker" {
  name   = "firecracker-${filesha256(var.firecracker_asset_path)}"
  bucket = google_storage_bucket.assets.name
  source = var.firecracker_asset_path
}

resource "google_storage_bucket_object" "jailer" {
  name   = "jailer-${filesha256(var.jailer_asset_path)}"
  bucket = google_storage_bucket.assets.name
  source = var.jailer_asset_path
}

resource "google_storage_bucket_object" "kernel" {
  name   = "vmlinux-${filesha256(var.kernel_asset_path)}"
  bucket = google_storage_bucket.assets.name
  source = var.kernel_asset_path
}

resource "google_artifact_registry_repository" "sshcloud" {
  location      = var.region
  repository_id = local.prefix
  description   = "sshcloud platform images (ko)"
  format        = "DOCKER"
  labels        = local.labels

  depends_on = [module.project_services]
}

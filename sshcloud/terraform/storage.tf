resource "google_storage_bucket" "snapshots" {
  name                        = "${local.prefix}-${var.project_id}-snaps"
  location                    = var.region
  uniform_bucket_level_access = true
  force_destroy               = false
  labels                      = local.labels

  depends_on = [google_project_service.services]
}

resource "google_storage_bucket" "assets" {
  name                        = "${local.prefix}-${var.project_id}-assets"
  location                    = var.region
  uniform_bucket_level_access = true
  force_destroy               = false
  labels                      = local.labels

  depends_on = [google_project_service.services]
}

resource "google_artifact_registry_repository" "sshcloud" {
  location      = var.region
  repository_id = local.prefix
  description   = "sshcloud platform images (ko)"
  format        = "DOCKER"
  labels        = local.labels

  depends_on = [google_project_service.services]
}

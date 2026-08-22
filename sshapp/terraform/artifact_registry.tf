resource "google_artifact_registry_repository" "apps" {
  location      = var.region
  repository_id = local.ar_repo_id
  description   = "Container images for sshapp Wish apps (ko_build)."
  format        = "DOCKER"

  mode = "STANDARD_REPOSITORY"

  depends_on = [google_project_service.services]
}

# Autopilot nodes pull images with the default Compute Engine SA.
resource "google_artifact_registry_repository_iam_member" "node_reader" {
  project    = var.project_id
  location   = google_artifact_registry_repository.apps.location
  repository = google_artifact_registry_repository.apps.name
  role       = "roles/artifactregistry.reader"
  member     = "serviceAccount:${data.google_project.current.number}-compute@developer.gserviceaccount.com"
}

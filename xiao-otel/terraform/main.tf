# IAM, IAM Credentials, STS, and Cloud Resource Manager are enabled by
# gcp/terraform, which owns the shared GitHub connection.
resource "google_project_service" "services" {
  for_each = toset([
    "artifactregistry.googleapis.com",
    "logging.googleapis.com",
    "monitoring.googleapis.com",
    "run.googleapis.com",
  ])

  service            = each.key
  disable_on_destroy = false
}

resource "google_artifact_registry_repository" "images" {
  repository_id = var.name
  location      = var.region
  format        = "DOCKER"

  depends_on = [google_project_service.services]
}

# gcp/terraform creates the runtime account. The deploy account can act
# as it but cannot create a service account.
data "google_service_account" "service" {
  account_id = var.name
}

resource "google_project_iam_member" "telemetry" {
  for_each = toset([
    "roles/logging.logWriter",
    "roles/monitoring.metricWriter",
  ])

  project = var.project_id
  role    = each.value
  member  = "serviceAccount:${data.google_service_account.service.email}"
}

resource "ko_build" "server" {
  importpath  = "github.com/imjasonh/playground/xiao-otel"
  working_dir = abspath("${path.module}/..")
  base_image  = "cgr.dev/chainguard/static"
  platforms   = ["linux/amd64"]
  sbom        = "none"

  env = [
    "CGO_ENABLED=0",
    "GOFLAGS=-buildvcs=false",
  ]
}

resource "google_cloud_run_v2_service" "service" {
  name     = var.name
  location = var.region
  ingress  = "INGRESS_TRAFFIC_ALL"

  template {
    execution_environment = "EXECUTION_ENVIRONMENT_GEN2"
    service_account       = data.google_service_account.service.email

    scaling {
      # Keep a single instance warm/shared so in-memory App Attest challenges
      # and counters stay on the same instance across the challenge -> POST pair.
      max_instance_count = 1
    }

    containers {
      image = ko_build.server.image_ref

      resources {
        limits = {
          cpu    = "1"
          memory = "512Mi"
        }
        cpu_idle          = true
        startup_cpu_boost = true
      }

      env {
        name  = "GOOGLE_CLOUD_PROJECT"
        value = var.project_id
      }
      env {
        name  = "APP_ID"
        value = var.app_id
      }
      env {
        name  = "ALLOW_UNATTESTED"
        value = tostring(var.allow_unattested)
      }
    }
  }

  depends_on = [
    google_project_service.services,
    google_project_iam_member.telemetry,
  ]
}

resource "google_cloud_run_v2_service_iam_member" "public" {
  count = var.public ? 1 : 0

  name     = google_cloud_run_v2_service.service.name
  location = google_cloud_run_v2_service.service.location
  role     = "roles/run.invoker"
  member   = "allUsers"
}

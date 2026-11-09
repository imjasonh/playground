# IAM, IAM Credentials, STS, and Cloud Resource Manager are enabled by
# gcp/terraform, which owns the shared GitHub connection.
resource "google_project_service" "services" {
  for_each = toset([
    "artifactregistry.googleapis.com",
    "run.googleapis.com",
    "storage.googleapis.com",
  ])

  service            = each.key
  disable_on_destroy = false
}

resource "google_storage_bucket" "replica" {
  name                        = "${var.project_id}-${var.name}"
  location                    = var.region
  uniform_bucket_level_access = true
  public_access_prevention    = "enforced"

  # The writer deletes superseded log entries and bases after each
  # snapshot. Soft delete would keep billing each one for seven days.
  soft_delete_policy {
    retention_duration_seconds = 0
  }
}

resource "google_artifact_registry_repository" "images" {
  repository_id = var.name
  location      = var.region
  format        = "DOCKER"

  depends_on = [google_project_service.services]
}

resource "google_service_account" "service" {
  account_id   = var.name
  display_name = "cloudrun-duckdb service"
}

resource "google_storage_bucket_iam_member" "replica" {
  bucket = google_storage_bucket.replica.name
  role   = "roles/storage.objectAdmin"
  member = "serviceAccount:${google_service_account.service.email}"
}

resource "ko_build" "server" {
  importpath  = "github.com/imjasonh/playground/cloudrun-duckdb"
  working_dir = abspath("${path.module}/..")
  # glibc-dynamic includes libstdc++, which DuckDB links.
  base_image = "cgr.dev/chainguard/glibc-dynamic"
  platforms  = ["linux/amd64"]
  sbom       = "none"

  # The DuckDB driver links DuckDB's prebuilt static library, which is C++
  # built against libstdc++.
  env = [
    "CGO_ENABLED=1",
    "CC=${var.cgo_cc}",
  ]
}

locals {
  replica_url = "gs://${google_storage_bucket.replica.name}/db"
}

resource "google_cloud_run_v2_service" "service" {
  name     = var.name
  location = var.region
  ingress  = "INGRESS_TRAFFIC_ALL"

  # The in-memory volume needs the second-generation runtime.
  template {
    execution_environment = "EXECUTION_ENVIRONMENT_GEN2"
    service_account       = google_service_account.service.email

    scaling {
      # One writer at a time. Cloud Run can briefly run more than this
      # (deploys, scaling); conditional log uploads keep that safe.
      max_instance_count = 1
    }

    # Concurrent writes share transactions and uploads.
    max_instance_request_concurrency = 1000

    containers {
      image = ko_build.server.image_ref

      resources {
        limits = {
          cpu    = "1"
          memory = var.memory_limit
        }
        cpu_idle          = !var.cpu_always_allocated
        startup_cpu_boost = true
      }

      env {
        name  = "REPLICA_URL"
        value = local.replica_url
      }
      env {
        name  = "DATA_DIR"
        value = "/scratch"
      }
      env {
        name  = "DURABLE"
        value = tostring(var.durable)
      }
      env {
        name  = "DUCKDB_MEMORY_LIMIT"
        value = var.duckdb_memory_limit
      }
      env {
        name  = "DUCKDB_THREADS"
        value = "1"
      }
      env {
        name  = "GOMEMLIMIT"
        value = var.go_memory_limit
      }

      volume_mounts {
        name       = "scratch"
        mount_path = "/scratch"
      }
    }

    volumes {
      name = "scratch"
      empty_dir {
        medium     = "MEMORY"
        size_limit = var.scratch_size_limit
      }
    }
  }

  depends_on = [
    google_project_service.services,
    google_storage_bucket_iam_member.replica,
  ]
}

resource "google_cloud_run_v2_service_iam_member" "public" {
  count = var.public ? 1 : 0

  name     = google_cloud_run_v2_service.service.name
  location = google_cloud_run_v2_service.service.location
  role     = "roles/run.invoker"
  member   = "allUsers"
}

# The read-only replica has its own account so that its bucket role can't
# write. The server also opens DuckDB read-only and refuses writes, but
# the role holds even if that code changes.
resource "google_service_account" "reader" {
  account_id   = "${var.name}-reader"
  display_name = "cloudrun-duckdb read-only replica"
}

# Gets and lists only: no uploads, deletes, or overwrites.
resource "google_storage_bucket_iam_member" "reader" {
  bucket = google_storage_bucket.replica.name
  role   = "roles/storage.objectViewer"
  member = "serviceAccount:${google_service_account.reader.email}"
}

# A separate service, so for now it has its own URL. A load balancer can
# later send GETs here and everything else to the writer.
resource "google_cloud_run_v2_service" "reader" {
  name     = "${var.name}-reader"
  location = var.region
  ingress  = "INGRESS_TRAFFIC_ALL"

  template {
    execution_environment = "EXECUTION_ENVIRONMENT_GEN2"
    service_account       = google_service_account.reader.email

    scaling {
      max_instance_count = var.reader_max_instances
    }

    max_instance_request_concurrency = 1000

    containers {
      image = ko_build.server.image_ref

      resources {
        limits = {
          cpu    = "1"
          memory = var.memory_limit
        }
        cpu_idle          = !var.cpu_always_allocated
        startup_cpu_boost = true
      }

      env {
        name  = "READ_ONLY"
        value = "true"
      }
      env {
        name  = "REPLICA_URL"
        value = local.replica_url
      }
      env {
        name  = "DATA_DIR"
        value = "/scratch"
      }
      env {
        name  = "POLL_INTERVAL"
        value = var.reader_poll_interval
      }
      env {
        name  = "WRITER_URL"
        value = google_cloud_run_v2_service.service.uri
      }
      env {
        name  = "DUCKDB_MEMORY_LIMIT"
        value = var.duckdb_memory_limit
      }
      env {
        name  = "DUCKDB_THREADS"
        value = "1"
      }
      env {
        name  = "GOMEMLIMIT"
        value = var.go_memory_limit
      }

      volume_mounts {
        name       = "scratch"
        mount_path = "/scratch"
      }
    }

    volumes {
      name = "scratch"
      empty_dir {
        medium     = "MEMORY"
        size_limit = var.scratch_size_limit
      }
    }
  }

  # A read-only open waits until the database exists, and the writer
  # creates it when its first instance starts.
  depends_on = [
    google_project_service.services,
    google_storage_bucket_iam_member.reader,
    google_cloud_run_v2_service.service,
  ]
}

resource "google_cloud_run_v2_service_iam_member" "reader_public" {
  count = var.public ? 1 : 0

  name     = google_cloud_run_v2_service.reader.name
  location = google_cloud_run_v2_service.reader.location
  role     = "roles/run.invoker"
  member   = "allUsers"
}

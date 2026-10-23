terraform {
  required_version = ">= 1.5.0"

  # GitHub Actions and a local apply share this state. Create the bucket
  # once, in this project, and pass it at init. The prefix leaves room
  # for another app to use the same bucket.
  #   terraform init -backend-config="bucket=BUCKET"
  backend "gcs" {
    prefix = "cloudrun-sqlite"
  }

  required_providers {
    google = {
      source  = "hashicorp/google"
      version = ">= 6.0.0, < 8.0.0"
    }
    ko = {
      source  = "ko-build/ko"
      version = ">= 0.0.12"
    }
  }
}

provider "google" {
  project = var.project_id
  region  = var.region
}

provider "ko" {
  repo = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.images.repository_id}"
}

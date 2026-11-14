terraform {
  required_version = ">= 1.5.0"

  # GitHub Actions and a local apply share this state. Create the bucket
  # once, in this project, and pass it at init:
  #   tofu init -backend-config="bucket=BUCKET"
  backend "gcs" {
    prefix = "stream-boids"
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
    apko = {
      source  = "chainguard-dev/apko"
      version = ">= 1.0.0"
    }
  }
}

provider "google" {
  project = var.project_id
  region  = var.region
}

locals {
  registry = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.images.repository_id}"
}

provider "ko" {
  repo = local.registry
}

# apk.cgr.dev needs a Chainguard token. apko exchanges the job's Google
# ID token for one when CHAINGUARD_IDENTITY names a Chainguard identity
# that trusts this account (see README.md). Locally, chainctl login works.
provider "apko" {}

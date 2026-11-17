terraform {
  required_version = ">= 1.5.0"

  # GitHub Actions and a local apply share this state. It lives in the
  # same bucket as the other app stacks, under this app's prefix.
  #   tofu init -backend-config="bucket=BUCKET"
  backend "gcs" {
    prefix = "wehadababyitsaboy"
  }

  required_providers {
    google = {
      source  = "hashicorp/google"
      version = ">= 6.0.0, < 8.0.0"
    }
  }
}

provider "google" {
  project = var.project_id
}

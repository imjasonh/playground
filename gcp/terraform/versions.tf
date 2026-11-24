terraform {
  required_version = ">= 1.5.0"

  # Same bucket as the app stacks, different prefix. Create the bucket
  # once and pass it at init:
  #   tofu init -backend-config="bucket=BUCKET"
  backend "gcs" {
    prefix = "github"
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

  # The Budgets API rejects user credentials that don't name a quota project.
  billing_project       = var.project_id
  user_project_override = true
}

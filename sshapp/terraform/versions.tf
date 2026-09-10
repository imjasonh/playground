terraform {
  required_version = ">= 1.5.0"

  # Remote state for CD. Local and CI pass bucket/prefix at init:
  #   terraform init -backend-config=bucket=… -backend-config=prefix=sshapp
  backend "gcs" {}

  required_providers {
    google = {
      source  = "hashicorp/google"
      version = ">= 5.40.0, < 7.0.0"
    }
    google-beta = {
      source  = "hashicorp/google-beta"
      version = ">= 5.40.0, < 7.0.0"
    }
    kubernetes = {
      source  = "hashicorp/kubernetes"
      version = ">= 2.30.0, < 3.0.0"
    }
    ko = {
      source  = "ko-build/ko"
      version = ">= 0.0.12"
    }
    tls = {
      source  = "hashicorp/tls"
      version = ">= 4.0.0"
    }
  }
}

provider "google" {
  project = var.project_id
  region  = var.region
}

provider "google-beta" {
  project = var.project_id
  region  = var.region
}

data "google_client_config" "default" {}

data "google_project" "current" {
  project_id = var.project_id
}

provider "kubernetes" {
  host                   = "https://${google_container_cluster.sshapp.endpoint}"
  token                  = data.google_client_config.default.access_token
  cluster_ca_certificate = base64decode(google_container_cluster.sshapp.master_auth[0].cluster_ca_certificate)
}

provider "ko" {
  repo = "${var.region}-docker.pkg.dev/${var.project_id}/${google_artifact_registry_repository.apps.repository_id}"
}

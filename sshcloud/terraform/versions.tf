terraform {
  required_version = ">= 1.6.0"

  # State contains private SSH and control-plane keys. Keep backend settings
  # out of source and initialize with backend.gcs.hcl; see the key-rotation
  # runbook for the one-time local-to-GCS migration and recovery procedure.
  backend "gcs" {}

  required_providers {
    google = {
      source  = "hashicorp/google"
      version = ">= 6.0.0, < 7.0.0"
    }
    ko = {
      source  = "ko-build/ko"
      version = ">= 0.0.17"
    }
    tls = {
      source  = "hashicorp/tls"
      version = ">= 4.0.0"
    }
  }
}

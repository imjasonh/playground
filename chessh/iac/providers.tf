terraform {
  required_version = ">= 1.5"

  required_providers {
    exedev = {
      source  = "benjamin-lykins/exedev"
      version = "~> 0.1"
    }
    ko = {
      source  = "ko-build/ko"
      version = "~> 0.0"
    }
  }

  # Partial S3 backend: CI mints R2 credentials from CLOUDFLARE_API_TOKEN and
  # passes the endpoint via -backend-config.
  # Local applies can use the same flags, or switch to a local backend override.
  backend "s3" {
    bucket = "playground-terraform-state"
    key    = "exe/chessh/terraform.tfstate"
    region = "auto"

    skip_credentials_validation = true
    skip_metadata_api_check     = true
    skip_region_validation      = true
    skip_requesting_account_id  = true
    skip_s3_checksum            = true
    use_path_style              = true
  }
}

provider "exedev" {
  # Token from EXEDEV_TOKEN (minted in CI from EXEDEV_SSH_PRIVATE_KEY).
}

provider "ko" {
  # Default repo; each ko_build.app.repo overrides to an exact GHCR path.
  repo = "ghcr.io/imjasonh/playground"
}

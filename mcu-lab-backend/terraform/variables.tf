variable "project_id" {
  description = "Google Cloud project that owns the service and image repository."
  type        = string
}

variable "region" {
  description = "Region for Cloud Run and Artifact Registry."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Name for the Cloud Run service, runtime service account, and image repository. Kept as xiao-otel to preserve the existing GCP service account, Terraform state, and live Cloud Run URL."
  type        = string
  default     = "xiao-otel"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{4,17}[a-z0-9]$", var.name))
    error_message = "name must be 6 to 19 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "app_id" {
  description = "Apple App ID (<Team ID>.<Bundle ID>) expected in App Attest authenticatorData."
  type        = string
  default     = "W5LPA2QM2W.io.github.imjasonh.playground"
}

variable "allow_unattested" {
  description = "Allow Simulator unattested tokens (leave false in production)."
  type        = bool
  default     = false
}

variable "public" {
  description = "Allow unauthenticated HTTP requests (App Attest authorizes every POST /v1/metrics call inside the server)."
  type        = bool
  default     = true
}

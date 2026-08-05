variable "project_id" {
  description = "GCP project whose required APIs are enabled"
  type        = string
}

variable "services" {
  description = "Google Cloud service APIs required by the platform"
  type        = set(string)
}

resource "google_project_service" "required" {
  for_each = var.services

  project                    = var.project_id
  service                    = each.value
  disable_on_destroy         = false
  disable_dependent_services = false
}

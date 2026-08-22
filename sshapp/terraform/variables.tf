variable "project_id" {
  description = "Google Cloud project ID that owns the cluster and registry."
  type        = string
}

variable "region" {
  description = "Region for the Autopilot cluster, Artifact Registry, and networking."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Short name used as a prefix for cluster, network, and DNS resources."
  type        = string
  default     = "sshapp"
}

variable "domain" {
  description = "DNS apex. Mux is ssh.<domain>; apps route as ssh user@ssh.<domain> <app> (and *.<domain> points at the same IP)."
  type        = string
}

variable "create_dns_zone" {
  description = "When true, create a Cloud DNS public zone for var.domain. When false, use dns_zone_name."
  type        = bool
  default     = true
}

variable "dns_zone_name" {
  description = "Existing Cloud DNS managed zone name. Used only when create_dns_zone is false."
  type        = string
  default     = ""

  validation {
    condition     = var.create_dns_zone || length(var.dns_zone_name) > 0
    error_message = "dns_zone_name must be set when create_dns_zone is false."
  }
}

variable "ssh_allowed_cidrs" {
  description = "CIDR ranges allowed to reach the shared mux LoadBalancer on port 22. Empty means 0.0.0.0/0."
  type        = list(string)
  default     = []
}

variable "mux_idle_after" {
  description = "How long the mux waits with zero connections to an app before scaling that app to zero."
  type        = string
  default     = "5m"
}

variable "master_authorized_cidrs" {
  description = "CIDR ranges allowed to reach the GKE control plane. Empty leaves the endpoint open to Google Cloud IPs used by Terraform and gcloud."
  type = list(object({
    cidr_block   = string
    display_name = string
  }))
  default = []
}

variable "deletion_protection" {
  description = "When true, Terraform cannot destroy the GKE cluster until flipped to false."
  type        = bool
  default     = true
}

variable "github_repository" {
  description = "GitHub repository (OWNER/REPO) for Workload Identity Federation. Leave empty to skip WIF resources."
  type        = string
  default     = ""
}

variable "apps" {
  description = "SSH apps to build with ko and deploy. Key is the mux route name (ssh user@ssh.domain <key>)."
  type = map(object({
    importpath    = string
    replicas      = optional(number, 1)
    scale_to_zero = optional(bool, true)
  }))
  default = {
    hello = {
      importpath    = "github.com/imjasonh/playground/sshapp/apps/hello"
      replicas      = 1
      scale_to_zero = true
    }
  }
}

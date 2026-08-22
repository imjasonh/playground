variable "name" {
  description = "App name and DNS label (<name>.domain)."
  type        = string
}

variable "namespace" {
  description = "Kubernetes namespace for the Deployment and Service."
  type        = string
}

variable "importpath" {
  description = "Go import path passed to ko_build for the Wish app."
  type        = string
}

variable "working_dir" {
  description = "Working directory for ko_build (module root that contains go.mod)."
  type        = string
}

variable "domain" {
  description = "DNS apex. The app is published at <name>.<domain>."
  type        = string
}

variable "dns_managed_zone" {
  description = "Cloud DNS managed zone name that holds records for domain."
  type        = string
}

variable "replicas" {
  description = "Warm replicas when the activator has traffic (ignored as a fixed count when scale_to_zero is true; activator owns scaling)."
  type        = number
  default     = 1
}

variable "scale_to_zero" {
  description = "When true, put a always-on activator in front of the app and let it scale the app Deployment 0↔replicas."
  type        = bool
  default     = true
}

variable "activator_importpath" {
  description = "Go import path for the activator binary."
  type        = string
  default     = "github.com/imjasonh/playground/sshapp/apps/activator"
}

variable "idle_after" {
  description = "How long the activator waits with zero connections before scaling the app to zero."
  type        = string
  default     = "5m"
}

variable "ssh_source_ranges" {
  description = "CIDRs allowed to connect to the LoadBalancer on port 22."
  type        = list(string)
}

variable "container_port" {
  description = "Port the Wish process (and activator) listen on inside the container."
  type        = number
  default     = 2222
}

variable "labels" {
  description = "Extra labels applied to Kubernetes objects."
  type        = map(string)
  default     = {}
}

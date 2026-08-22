variable "name" {
  description = "App name and DNS label (<name>.domain)."
  type        = string
}

variable "namespace" {
  description = "Kubernetes namespace for the Deployment and Service."
  type        = string
}

variable "importpath" {
  description = "Go import path passed to ko_build."
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
  description = "Desired pod replicas."
  type        = number
  default     = 2
}

variable "ssh_source_ranges" {
  description = "CIDRs allowed to connect to the LoadBalancer on port 22."
  type        = list(string)
}

variable "container_port" {
  description = "Port the Wish process listens on inside the container."
  type        = number
  default     = 2222
}

variable "labels" {
  description = "Extra labels applied to Kubernetes objects."
  type        = map(string)
  default     = {}
}

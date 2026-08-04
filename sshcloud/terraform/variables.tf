variable "project_id" {
  description = "GCP project ID"
  type        = string
}

variable "region" {
  description = "Primary region (one region in v1)"
  type        = string
  default     = "us-central1"
}

variable "zone" {
  description = "Zone for gateway, orchestrator, and the agent MIG"
  type        = string
  default     = "us-central1-a"
}

variable "name_prefix" {
  description = "Resource name prefix"
  type        = string
  default     = "sshcloud"
}

variable "firestore_location" {
  description = "Firestore location_id (nam5 = US multi-region, or a region like us-central1)"
  type        = string
  default     = "nam5"
}

variable "agent_count" {
  description = "Host MIG target size"
  type        = number
  default     = 2
}

variable "agent_machine_type" {
  description = "Machine type for Firecracker hosts (needs nested virt)"
  type        = string
  default     = "n2-standard-4"
}

variable "gateway_machine_type" {
  description = "Machine type for the public SSH gateway"
  type        = string
  default     = "e2-medium"
}

variable "orchestrator_machine_type" {
  description = "Machine type for the orchestrator VM"
  type        = string
  default     = "e2-small"
}

variable "gateway_disk_gb" {
  type    = number
  default = 20
}

variable "orchestrator_disk_gb" {
  type    = number
  default = 20
}

variable "agent_disk_gb" {
  description = "Boot disk size for agent hosts (rootfs cache + local snap working set)"
  type        = number
  default     = 50
}

variable "ssh_client_cidrs" {
  description = "CIDRs allowed to reach gateway TCP/22. Empty = 0.0.0.0/0."
  type        = list(string)
  default     = ["0.0.0.0/0"]
}

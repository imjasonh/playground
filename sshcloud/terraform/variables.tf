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

variable "firestore_database" {
  description = "Dedicated Firestore database ID used only by sshcloud"
  type        = string
  default     = "sshcloud"
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{3,62}$", var.firestore_database))
    error_message = "firestore_database must be 4-63 lowercase letters, digits, or hyphens."
  }
}

variable "firestore_prefix" {
  description = "Collection prefix used to isolate sshcloud data in a shared Firestore database"
  type        = string
  default     = "sshcloud"
  validation {
    condition     = can(regex("^[a-z][a-z0-9_-]{2,31}$", var.firestore_prefix))
    error_message = "firestore_prefix must match [a-z][a-z0-9_-]{2,31}."
  }
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
  description = "CIDRs allowed to reach public gateway TCP/22. Empty keeps public SSH closed."
  type        = list(string)
  default     = []
}

variable "member_ssh_public_keys" {
  description = "Operator-configured OpenSSH public key lines allowed to join and use sshcloud when access_join_mode is allowlist"
  type        = list(string)
  default     = []
  validation {
    condition = alltrue([
      for key in var.member_ssh_public_keys :
      trimspace(key) != "" &&
      !strcontains(trimspace(key), "\n") &&
      !strcontains(trimspace(key), "\r")
    ])
    error_message = "member_ssh_public_keys entries must each contain one non-empty OpenSSH public key line."
  }
}

variable "deployer_ssh_public_keys" {
  description = "Operator-configured OpenSSH public key lines allowed to deploy; deployer keys also imply membership"
  type        = list(string)
  default     = []
  validation {
    condition = alltrue([
      for key in var.deployer_ssh_public_keys :
      trimspace(key) != "" &&
      !strcontains(trimspace(key), "\n") &&
      !strcontains(trimspace(key), "\r")
    ])
    error_message = "deployer_ssh_public_keys entries must each contain one non-empty OpenSSH public key line."
  }
}

variable "access_join_mode" {
  description = "SSH-key admission mode: allowlist or open"
  type        = string
  default     = "allowlist"
  validation {
    condition     = contains(["allowlist", "open"], var.access_join_mode)
    error_message = "access_join_mode must be allowlist or open."
  }
}

variable "access_deploy_mode" {
  description = "Deploy admission mode: allowlist or all-users"
  type        = string
  default     = "allowlist"
  validation {
    condition     = contains(["allowlist", "all-users"], var.access_deploy_mode)
    error_message = "access_deploy_mode must be allowlist or all-users."
  }
}

variable "firecracker_asset_path" {
  description = "Local path to the pinned Firecracker binary uploaded into the platform-assets bucket"
  type        = string
}

variable "jailer_asset_path" {
  description = "Local path to the matching pinned Firecracker jailer binary uploaded into the platform-assets bucket"
  type        = string
}

variable "kernel_asset_path" {
  description = "Local path to the pinned Firecracker-compatible vmlinux uploaded into the platform-assets bucket"
  type        = string
}

variable "enable_demo_bootstrap" {
  description = "Opt in to local-exec SSH join+deploy for the fortune smoke-test app"
  type        = bool
  default     = false
}

variable "demo_user" {
  description = "Username created by the optional fortune bootstrap"
  type        = string
  default     = "demo"
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{2,31}$", var.demo_user))
    error_message = "demo_user must match [a-z][a-z0-9-]{2,31}."
  }
}

variable "demo_app" {
  description = "App name used by the optional fortune bootstrap"
  type        = string
  default     = "fortune"
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{2,31}$", var.demo_app))
    error_message = "demo_app must match [a-z][a-z0-9-]{2,31}."
  }
}

variable "demo_tier" {
  description = "Resource tier for the optional fortune bootstrap"
  type        = string
  default     = "tiny"
  validation {
    condition     = contains(["tiny", "small"], var.demo_tier)
    error_message = "demo_tier must be tiny or small."
  }
}

variable "demo_strategy" {
  description = "Session cutover strategy for the optional fortune bootstrap"
  type        = string
  default     = "kick"
  validation {
    condition     = contains(["kick", "drain"], var.demo_strategy)
    error_message = "demo_strategy must be kick or drain."
  }
}

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

variable "user_firestore_database" {
  description = "Dedicated Firestore database ID for users, apps, keys, and quota counters"
  type        = string
  default     = "sshcloud-user"
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{3,62}$", var.user_firestore_database))
    error_message = "user_firestore_database must be 4-63 lowercase letters, digits, or hyphens."
  }
}

variable "placement_firestore_database" {
  description = "Dedicated Firestore database ID for placement and operation journals"
  type        = string
  default     = "sshcloud-placement"
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{3,62}$", var.placement_firestore_database))
    error_message = "placement_firestore_database must be 4-63 lowercase letters, digits, or hyphens."
  }
}

check "firestore_databases_are_distinct" {
  assert {
    condition     = var.user_firestore_database != var.placement_firestore_database
    error_message = "user_firestore_database and placement_firestore_database must be different named databases."
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

variable "control_ca_active_slot" {
  description = "Control PKI signing slot. This selects the leaf issuer only; both fixed A/B trust slots remain distributed."
  type        = string
  default     = "a"
  validation {
    condition     = contains(["a", "b"], var.control_ca_active_slot)
    error_message = "control_ca_active_slot must be a or b."
  }
}

variable "control_ca_rotation_epochs" {
  description = "Explicit non-negative epochs for deterministic A/B CA key replacement. Increment only the inactive slot after following the rotation runbook."
  type        = map(number)
  default = {
    a = 0
    b = 0
  }
  validation {
    condition = (
      length(var.control_ca_rotation_epochs) == 2 &&
      alltrue([
        for slot in ["a", "b"] :
        try(
          var.control_ca_rotation_epochs[slot] >= 0 &&
          var.control_ca_rotation_epochs[slot] == floor(var.control_ca_rotation_epochs[slot]),
          false,
        )
      ])
    )
    error_message = "control_ca_rotation_epochs must contain exactly a and b with non-negative integer values."
  }
}

variable "control_leaf_rotation_epochs" {
  description = "Explicit non-negative epochs for role leaf key/certificate replacement. Increment one role at a time and verify dynamic reload."
  type        = map(number)
  default = {
    gateway      = 0
    orchestrator = 0
    agent        = 0
    snapshot     = 0
  }
  validation {
    condition = (
      length(var.control_leaf_rotation_epochs) == 4 &&
      alltrue([
        for role in ["gateway", "orchestrator", "agent", "snapshot"] :
        try(
          var.control_leaf_rotation_epochs[role] >= 0 &&
          var.control_leaf_rotation_epochs[role] == floor(var.control_leaf_rotation_epochs[role]),
          false,
        )
      ])
    )
    error_message = "control_leaf_rotation_epochs must contain exactly gateway, orchestrator, agent, and snapshot with non-negative integer values."
  }
}

variable "gateway_host_key_rotation_epoch" {
  description = "Explicit non-negative epoch for planned gateway SSH host-key replacement. Follow the pinned known_hosts maintenance procedure before incrementing."
  type        = number
  default     = 0
  validation {
    condition = (
      var.gateway_host_key_rotation_epoch >= 0 &&
      var.gateway_host_key_rotation_epoch == floor(var.gateway_host_key_rotation_epoch)
    )
    error_message = "gateway_host_key_rotation_epoch must be a non-negative integer."
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

variable "snapshot_machine_type" {
  description = "Machine type for the private snapshot proxy"
  type        = string
  default     = "e2-standard-2"
}

variable "gateway_disk_gb" {
  type    = number
  default = 20
}

variable "orchestrator_disk_gb" {
  type    = number
  default = 20
}

variable "snapshot_disk_gb" {
  description = "Boot/staging disk size for snapshotd package proxying"
  type        = number
  default     = 20
}

variable "snapshot_staging_max_bytes" {
  description = "Global weighted plaintext staging reservation for snapshotd"
  type        = number
  default     = 10737418240
  validation {
    condition = (
      var.snapshot_staging_max_bytes >= 4429250560 &&
      var.snapshot_staging_max_bytes == floor(var.snapshot_staging_max_bytes)
    )
    error_message = "snapshot_staging_max_bytes must be an integer that fits one maximum package."
  }
}

check "snapshot_staging_disk_capacity" {
  assert {
    condition     = var.snapshot_staging_max_bytes <= (var.snapshot_disk_gb - 5) * 1073741824
    error_message = "snapshot_staging_max_bytes must leave 5 GiB of snapshotd disk unreserved."
  }
}

variable "snapshot_staging_max_operations" {
  description = "Maximum concurrent snapshotd plaintext staging operations"
  type        = number
  default     = 2
  validation {
    condition = (
      var.snapshot_staging_max_operations >= 1 &&
      var.snapshot_staging_max_operations <= 8 &&
      var.snapshot_staging_max_operations == floor(var.snapshot_staging_max_operations)
    )
    error_message = "snapshot_staging_max_operations must be an integer from 1 through 8."
  }
}

variable "snapshot_staging_max_per_agent" {
  description = "Maximum concurrent snapshotd staging operations per exact agent incarnation"
  type        = number
  default     = 1
  validation {
    condition = (
      var.snapshot_staging_max_per_agent >= 1 &&
      var.snapshot_staging_max_per_agent == floor(var.snapshot_staging_max_per_agent)
    )
    error_message = "snapshot_staging_max_per_agent must be a positive integer."
  }
}

check "snapshot_staging_concurrency" {
  assert {
    condition     = var.snapshot_staging_max_per_agent <= var.snapshot_staging_max_operations
    error_message = "snapshot_staging_max_per_agent must not exceed snapshot_staging_max_operations."
  }
}

variable "agent_disk_gb" {
  description = "Boot disk size for agent hosts (rootfs cache + local snap working set)"
  type        = number
  default     = 50
}

variable "agent_rootfs_cache_bytes" {
  description = "Hard per-host OCI rootfs cache budget; LRU eviction runs before materialization"
  type        = number
  default     = 8589934592
  validation {
    condition     = var.agent_rootfs_cache_bytes >= 1073741824 && var.agent_rootfs_cache_bytes <= 34359738368
    error_message = "agent_rootfs_cache_bytes must be between 1 GiB and 32 GiB."
  }
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

variable "notification_email" {
  description = "Optional email address for core Monitoring alerts and budget notifications"
  type        = string
  default     = null
  nullable    = true
  validation {
    condition     = var.notification_email == null ? true : can(regex("^[^@[:space:]]+@[^@[:space:]]+\\.[^@[:space:]]+$", var.notification_email))
    error_message = "notification_email must be null or a valid email address."
  }
}

variable "billing_account_id" {
  description = "Optional billing account ID used with monthly_budget_usd"
  type        = string
  default     = null
  nullable    = true
  validation {
    condition     = var.billing_account_id == null ? true : can(regex("^[0-9A-F]{6}-[0-9A-F]{6}-[0-9A-F]{6}$", var.billing_account_id))
    error_message = "billing_account_id must look like 000000-000000-000000."
  }
}

variable "monthly_budget_usd" {
  description = "Optional whole-dollar monthly project budget; requires billing_account_id"
  type        = number
  default     = null
  nullable    = true
  validation {
    condition = var.monthly_budget_usd == null ? true : (
      var.monthly_budget_usd >= 1 && var.monthly_budget_usd == floor(var.monthly_budget_usd)
    )
    error_message = "monthly_budget_usd must be null or a positive whole-dollar amount."
  }
}

check "billing_budget_inputs" {
  assert {
    condition     = (var.billing_account_id == null) == (var.monthly_budget_usd == null)
    error_message = "billing_account_id and monthly_budget_usd must be set together."
  }
}

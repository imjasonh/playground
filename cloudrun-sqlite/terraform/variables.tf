variable "project_id" {
  description = "Google Cloud project that owns the service, bucket, and image repository."
  type        = string
}

variable "region" {
  description = "Region for Cloud Run, the bucket, and Artifact Registry. Keep them together; every cold page read is a request to the bucket."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Name for the service, service account, image repository, and the GitHub environment gcp-<name>. Use the app directory name."
  type        = string
  default     = "cloudrun-sqlite"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{4,17}[a-z0-9]$", var.name))
    error_message = "name must be 6 to 19 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen. Service account ids are 6 to 30 characters, and the deploy account id is <name>-gha-deploy."
  }
}

variable "durable" {
  description = "Acknowledge writes only after they are in Cloud Storage. When false, a crash loses up to one second of acknowledged writes."
  type        = bool
  default     = true
}

variable "hydrate" {
  description = "Download the whole database to the instance in the background. Needs memory for the database on top of memory_limit's other uses."
  type        = bool
  default     = false
}

variable "cpu_always_allocated" {
  description = "Use instance-based billing so compaction and snapshots run between requests. With request-based billing they run only while requests are in flight."
  type        = bool
  default     = false
}

variable "memory_limit" {
  description = "Container memory. The page cache, the page index (about 75 MiB per GiB of database), the write buffer, and any hydrated copy count against it."
  type        = string
  default     = "512Mi"
}

variable "go_memory_limit" {
  description = "GOMEMLIMIT for the server, about 80% of memory_limit, so the Go runtime collects garbage before Cloud Run's limit kills the instance."
  type        = string
  default     = "400MiB"
}

variable "scratch_size_limit" {
  description = "Size limit of the in-memory volume that holds the write buffer and hydrated copy."
  type        = string
  default     = "256Mi"
}

variable "public" {
  description = "Allow unauthenticated requests."
  type        = bool
  default     = true
}

variable "cgo_cc" {
  description = "C compiler for the CGO build. The default cross-compiles with zig from any host; on linux/amd64 with gcc, use \"gcc\"."
  type        = string
  default     = "zig cc -target x86_64-linux-gnu"
}

variable "github_repository" {
  description = "GitHub repository (OWNER/REPO) allowed to deploy this service. Leave empty to skip the deploy and plan service accounts. The Workload Identity pool itself lives in gcp/terraform."
  type        = string
  default     = ""

  validation {
    condition     = var.github_repository == "" || can(regex("^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$", var.github_repository))
    error_message = "github_repository must be empty or OWNER/REPO."
  }
}

variable "workload_identity_pool_id" {
  description = "Workload Identity pool from gcp/terraform. This stack binds service accounts to that pool. It does not create one."
  type        = string
  default     = "github"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{2,30}[a-z0-9]$", var.workload_identity_pool_id))
    error_message = "workload_identity_pool_id must be 4 to 32 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "github_environment" {
  description = "GitHub environment that must be selected to deploy or plan. Empty uses gcp-<name>, which is what deploy-gcp.yml selects."
  type        = string
  default     = ""

  validation {
    condition     = var.github_environment == "" || can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]{0,254}$", var.github_environment))
    error_message = "github_environment must be empty or a GitHub environment name."
  }
}

variable "state_bucket" {
  description = "Cloud Storage bucket that holds Terraform state. Required when github_repository is set, so the plan account can read state. Same bucket as terraform init -backend-config."
  type        = string
  default     = ""

  validation {
    condition     = var.state_bucket == "" || can(regex("^[a-z0-9][a-z0-9._-]{1,61}[a-z0-9]$", var.state_bucket))
    error_message = "state_bucket must be empty or a Cloud Storage bucket name."
  }
}

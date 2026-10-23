variable "project_id" {
  description = "Google Cloud project that trusts GitHub Actions."
  type        = string
}

variable "github_repository" {
  description = "GitHub repository (OWNER/REPO) allowed to deploy and plan."
  type        = string

  validation {
    condition     = can(regex("^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$", var.github_repository))
    error_message = "github_repository must be OWNER/REPO."
  }
}

variable "github_workflow" {
  description = "Workflow path that may deploy and plan, relative to the repository root. The pool rejects tokens from any other workflow."
  type        = string
  default     = ".github/workflows/deploy-gcp.yml"

  validation {
    condition     = can(regex("^\\.github/workflows/[A-Za-z0-9_.-]+\\.yml$", var.github_workflow))
    error_message = "github_workflow must be a workflow file under .github/workflows/."
  }
}

variable "pool_id" {
  description = "Workload Identity pool id. Apps bind service accounts to this id."
  type        = string
  default     = "github"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{2,30}[a-z0-9]$", var.pool_id))
    error_message = "pool_id must be 4 to 32 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "environment_prefix" {
  description = "GitHub environment prefix this pool accepts. deploy-gcp.yml selects gcp-<app>."
  type        = string
  default     = "gcp-"

  validation {
    condition     = can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]*$", var.environment_prefix))
    error_message = "environment_prefix must be a GitHub environment name prefix."
  }
}

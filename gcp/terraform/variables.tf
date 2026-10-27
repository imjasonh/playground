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
  description = "Workload Identity pool id."
  type        = string
  default     = "github"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{2,30}[a-z0-9]$", var.pool_id))
    error_message = "pool_id must be 4 to 32 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "github_environment" {
  description = "GitHub environment deploy-gcp.yml selects. The deploy and plan accounts accept only this name."
  type        = string
  default     = "gcp"

  validation {
    condition     = can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]{0,254}$", var.github_environment))
    error_message = "github_environment must be a GitHub environment name."
  }
}

variable "chrome_webstore_github_workflow" {
  description = "Workflow path allowed to mint a Chrome Web Store access token, relative to the repository root. The pool rejects tokens from any other workflow."
  type        = string
  default     = ".github/workflows/chrome-extension.yml"

  validation {
    condition     = can(regex("^\\.github/workflows/[A-Za-z0-9_.-]+\\.yml$", var.chrome_webstore_github_workflow))
    error_message = "chrome_webstore_github_workflow must be a workflow file under .github/workflows/."
  }
}

variable "chrome_webstore_github_environment" {
  description = "GitHub environment chrome-extension.yml selects for the publish job. The Chrome Web Store service account accepts only this environment."
  type        = string
  default     = "chrome-webstore"

  validation {
    condition     = can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]{0,254}$", var.chrome_webstore_github_environment))
    error_message = "chrome_webstore_github_environment must be a GitHub environment name."
  }
}

variable "state_bucket" {
  description = "Cloud Storage bucket that holds Terraform state for this stack and for app stacks. The plan account can read objects in this bucket only. Pass the same name to tofu init -backend-config."
  type        = string

  validation {
    condition     = can(regex("^[a-z0-9][a-z0-9._-]{1,61}[a-z0-9]$", var.state_bucket))
    error_message = "state_bucket must be a Cloud Storage bucket name."
  }
}

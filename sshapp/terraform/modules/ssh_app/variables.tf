variable "name" {
  description = "App name. Also the mux route key (ssh user@ssh.domain <name>)."
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

variable "replicas" {
  description = "Warm replicas the mux scales to when the app has traffic."
  type        = number
  default     = 1
}

variable "scale_to_zero" {
  description = "When true, Terraform leaves the Deployment at 0 replicas; the mux scales 0↔replicas."
  type        = bool
  default     = true
}

variable "deployment_strategy" {
  description = "Deployment strategy. Use Recreate when matchmaking is in-process so rolls never run two pods."
  type        = string
  default     = "RollingUpdate"

  validation {
    condition     = contains(["RollingUpdate", "Recreate"], var.deployment_strategy)
    error_message = "deployment_strategy must be RollingUpdate or Recreate."
  }
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

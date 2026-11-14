variable "project_id" {
  description = "Google Cloud project that owns the VM, secrets, and image repository."
  type        = string
}

variable "region" {
  description = "Region for the VM and Artifact Registry. The managed instance group recreates a preempted VM in any zone of this region."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Name for the instance group, service account, network, and image repository. Use the app directory name."
  type        = string
  default     = "stream-boids"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{4,17}[a-z0-9]$", var.name))
    error_message = "name must be 6 to 19 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "machine_type" {
  description = "Spot machine type. At 10,000 boids, 1080p60, and the faster preset, the stream uses about 4 vCPUs."
  type        = string
  default     = "c3-highcpu-8"
}

variable "running" {
  description = "Run the VM. Set to false to stop streaming and stop paying for the VM."
  type        = bool
  default     = true
}

variable "channel_id" {
  description = "YouTube channel ID (UC...). The service searches it for the live broadcast. Empty, with video_id empty, shows a fixed viewer count."
  type        = string
  default     = ""
}

variable "video_id" {
  description = "YouTube video ID of the scheduled broadcast. Saves the 100-unit search that channel_id costs."
  type        = string
  default     = ""
}

variable "boid_cap" {
  description = "Most boids on screen: one per viewer up to this many."
  type        = number
  default     = 10000
}

variable "x264_preset" {
  description = "x264 preset. Slower presets look better at the same bitrate and use more CPU."
  type        = string
  default     = "faster"
}

variable "video_bitrate" {
  description = "Video bitrate in bits per second. YouTube recommends 12 Mbps for 1080p60. Egress to YouTube is most of the cost."
  type        = number
  default     = 12000000
}

variable "log_level" {
  description = "LOG_LEVEL for the service."
  type        = string
  default     = "info"
}

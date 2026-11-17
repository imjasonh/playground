variable "project_id" {
  description = "Google Cloud project that owns both buckets."
  type        = string
}

variable "location" {
  description = "Location of both buckets."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Name of the empty bucket that clients request. Bucket names are global, and the client snippets in the README use this one. The usage logs go to a second bucket named NAME-logs."
  type        = string
  default     = "wehadababyitsaboy"

  validation {
    condition     = can(regex("^[a-z0-9][a-z0-9_-]{1,56}[a-z0-9]$", var.name))
    error_message = "name must be a bucket name of 3 to 58 characters, so that NAME-logs is also a bucket name."
  }
}

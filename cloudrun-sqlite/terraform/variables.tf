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
  description = "Name for the service, runtime service account, and image repository. Use the app directory name."
  type        = string
  default     = "cloudrun-sqlite"

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{4,17}[a-z0-9]$", var.name))
    error_message = "name must be 6 to 19 characters: a lowercase letter, then letters, digits, or hyphens, and it cannot end with a hyphen."
  }
}

variable "durable" {
  description = "Acknowledge writes only after they are in Cloud Storage. When false, a crash loses up to one second of acknowledged writes."
  type        = bool
  default     = true
}

variable "reader_max_instances" {
  description = "Most instances of the read-only replica service. Each instance with an open page lists the bucket every reader_poll_interval."
  type        = number
  default     = 3
}

variable "reader_poll_interval" {
  description = "How often each read-only replica instance lists the bucket for new writes, as a Go duration. A click reaches a replica page up to this long after the writer uploads it. At 2s, an instance kept busy by an open page makes 3,600 LIST requests an hour."
  type        = string
  default     = "2s"
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


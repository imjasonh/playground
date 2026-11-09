variable "project_id" {
  description = "Google Cloud project that owns the service, bucket, and image repository."
  type        = string
}

variable "region" {
  description = "Region for Cloud Run, the bucket, and Artifact Registry. Keep them together; every cold start downloads the database from the bucket."
  type        = string
  default     = "us-central1"
}

variable "name" {
  description = "Name for the service, runtime service account, and image repository. Use the app directory name."
  type        = string
  default     = "cloudrun-duckdb"

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
  description = "How often each read-only replica instance lists the bucket for new commits, as a Go duration. At 2s, an instance kept busy by an open page makes 1,800 LIST requests an hour."
  type        = string
  default     = "2s"
}

variable "cpu_always_allocated" {
  description = "Use instance-based billing. With request-based billing, a read-only replica polls only while requests are in flight."
  type        = bool
  default     = false
}

variable "memory_limit" {
  description = "Container memory. The in-memory volume (the whole database and its WAL), DuckDB's memory_limit, and the Go heap count against it."
  type        = string
  default     = "512Mi"
}

variable "scratch_size_limit" {
  description = "Size limit of the in-memory volume that holds the database file and its WAL. The database must fit, and a read-only replica briefly holds two copies while it switches to a new base."
  type        = string
  default     = "256Mi"
}

variable "duckdb_memory_limit" {
  description = "DuckDB's memory_limit: its buffer pool, which caches blocks of the local file on top of the file itself."
  type        = string
  default     = "128MB"
}

variable "go_memory_limit" {
  description = "GOMEMLIMIT for the server. DuckDB allocates outside the Go heap, so this is small."
  type        = string
  default     = "100MiB"
}

variable "public" {
  description = "Allow unauthenticated requests."
  type        = bool
  default     = true
}

variable "cgo_cc" {
  description = "C compiler for the CGO build. DuckDB's prebuilt library needs libstdc++, so zig's libc++ can't link it; build on linux/amd64 with gcc, as GitHub Actions does."
  type        = string
  default     = "gcc"
}

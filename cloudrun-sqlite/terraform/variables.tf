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
  description = "Name for the service, service account, and image repository."
  type        = string
  default     = "cloudrun-sqlite"
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
  description = "Container memory. The page cache, write buffer, and any hydrated copy count against it."
  type        = string
  default     = "512Mi"
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

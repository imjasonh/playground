variable "project_id" {
  description = "Google Cloud project that owns the service, bucket, and image repository."
  type        = string
}

variable "region" {
  description = "Region for Cloud Run and Artifact Registry. The Rapid replica bucket uses one zone in this region."
  type        = string
  default     = "us-central1"
}

variable "zone" {
  description = "Zone for the Rapid replica bucket. Empty uses the b zone of region. Rapid stores the database in this one zone."
  type        = string
  default     = ""
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

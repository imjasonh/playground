# An empty bucket that clients request, and a bucket for its usage logs.
#
# Cloud Storage writes an hourly CSV of every request to the empty bucket
# into the logs bucket: time, client IP, method, full URI with the query
# string, status, referrer, and User-Agent. Usage logs cost nothing to
# write, only to store.
#
# Cloud Audit Logs and a Logs Router sink can't do this job. Audit logs
# skip requests that allUsers access serves, and an <img> request carries
# no credentials. Audit logs also don't record arbitrary query strings,
# so a sink can't filter on ?bob=.
#
# Usage logs can't be filtered as Cloud Storage writes them, so every
# request is logged. report.sh keeps the rows whose URI has ?bob=.

resource "google_project_service" "storage" {
  service            = "storage.googleapis.com"
  disable_on_destroy = false
}

resource "google_storage_bucket" "logs" {
  name                        = "${var.name}-logs"
  location                    = var.location
  uniform_bucket_level_access = true
  public_access_prevention    = "enforced"

  depends_on = [google_project_service.storage]
}

resource "google_storage_bucket_iam_member" "logs_writer" {
  bucket = google_storage_bucket.logs.name
  role   = "roles/storage.objectCreator"
  member = "group:cloud-storage-analytics@google.com"
}

# Nobody can read this bucket, so every request fails with 403 and writes
# one usage log row. It holds no objects.
resource "google_storage_bucket" "pixel" {
  name                        = var.name
  location                    = var.location
  uniform_bucket_level_access = true
  public_access_prevention    = "enforced"

  logging {
    log_bucket        = google_storage_bucket.logs.name
    log_object_prefix = "usage"
  }

  depends_on = [google_storage_bucket_iam_member.logs_writer]
}

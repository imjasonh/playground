output "url" {
  value = google_cloud_run_v2_service.service.uri
}

output "reader_url" {
  value = google_cloud_run_v2_service.reader.uri
}

output "image" {
  value = ko_build.server.image_ref
}

output "replica_url" {
  value = local.replica_url
}

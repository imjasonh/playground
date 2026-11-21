output "url" {
  value = google_cloud_run_v2_service.service.uri
}

output "image" {
  value = ko_build.server.image_ref
}

output "service_account" {
  value = google_service_account.service.email
}

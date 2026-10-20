output "url" {
  value = google_cloud_run_v2_service.service.uri
}

output "image" {
  value = ko_build.server.image_ref
}

output "replica_url" {
  value = "gs://${google_storage_bucket.replica.name}/db"
}

output "dashboard_url" {
  value = "https://console.cloud.google.com/monitoring/dashboards/custom/${basename(google_monitoring_dashboard.latency.id)}?project=${var.project_id}"
}

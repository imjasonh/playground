output "url" {
  description = "The channel's live page, or YouTube Studio when no channel is set."
  value       = var.channel_id != "" ? "https://www.youtube.com/channel/${var.channel_id}/live" : (var.video_id != "" ? "https://www.youtube.com/watch?v=${var.video_id}" : "https://studio.youtube.com/")
}

output "image" {
  value = ko_build.app.image_ref
}

output "service_account" {
  value = google_service_account.vm.email
}

output "add_secrets" {
  description = "Commands that add the secret values. Each reads the value from standard input."
  value = join("\n", [
    for s in google_secret_manager_secret.secrets :
    "gcloud secrets versions add ${s.secret_id} --project=${var.project_id} --data-file=-"
  ])
}

output "logs" {
  value = "https://console.cloud.google.com/logs/query;query=resource.type%3D%22gce_instance%22%20logName%3D%22projects%2F${var.project_id}%2Flogs%2Fcos_containers%22?project=${var.project_id}"
}

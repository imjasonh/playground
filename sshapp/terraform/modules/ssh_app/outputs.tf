output "name" {
  description = "App name (Deployment / Service / mux route key)."
  value       = var.name
}

output "image_ref" {
  description = "ko image reference for the Wish app."
  value       = ko_build.app.image_ref
}

output "scale_to_zero" {
  description = "Whether the mux owns scaling for this app."
  value       = var.scale_to_zero
}

output "replicas" {
  description = "Warm replica count the mux scales to."
  value       = var.replicas
}

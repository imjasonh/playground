output "name" {
  description = "App name / DNS label."
  value       = var.name
}

output "fqdn" {
  description = "Public SSH hostname."
  value       = local.fqdn
}

output "image_ref" {
  description = "ko_build image reference by digest."
  value       = ko_build.app.image_ref
}

output "load_balancer_ip" {
  description = "External IP of the SSH LoadBalancer."
  value = try(
    one([
      for ingress in kubernetes_service_v1.app.status[0].load_balancer[0].ingress : ingress.ip
      if ingress.ip != null && ingress.ip != ""
    ]),
    null,
  )
}

output "host_key_fingerprint_sha256" {
  description = "SHA-256 fingerprint of the SSH host public key (OpenSSH format)."
  value       = tls_private_key.host.public_key_fingerprint_sha256
}

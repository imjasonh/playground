# Hacky sample-app bootstrap: after gateway (+ agents) are up, join as "demo"
# and `ssh deploy@… fortune --image=<ko digest> …` so fortune exists for a
# first `ssh fortune@GATEWAY` without a human TUI session.

resource "tls_private_key" "demo" {
  algorithm = "ED25519"
}

resource "terraform_data" "deploy_fortune" {
  input = {
    fortune_image = ko_build.fortune.image_ref
    gateway_id    = google_compute_instance.gateway.instance_id
    gateway_ip    = google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip
    agents        = google_compute_instance_group_manager.agents.id
  }

  depends_on = [
    google_compute_instance.gateway,
    google_compute_instance_group_manager.agents,
    google_compute_instance.orchestrator,
    ko_build.fortune,
  ]

  provisioner "local-exec" {
    interpreter = ["bash", "-c"]
    environment = {
      DEMO_KEY_PEM = tls_private_key.demo.private_key_openssh
      HOST_PUB     = tls_private_key.gateway_host.public_key_openssh
    }
    command = <<-EOT
      bash "${path.module}/scripts/deploy-fortune.sh" \
        "${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}" \
        "${ko_build.fortune.image_ref}"
    EOT
  }
}

# Hacky sample-app bootstrap: after gateway (+ agents) are up, join as "demo"
# and `ssh deploy@… fortune --image=<ko digest> …` so fortune exists for a
# first `ssh fortune@GATEWAY` without a human TUI session.

resource "tls_private_key" "demo" {
  count     = var.enable_demo_bootstrap ? 1 : 0
  algorithm = "ED25519"
}

resource "terraform_data" "deploy_fortune" {
  count = var.enable_demo_bootstrap ? 1 : 0

  triggers_replace = [
    ko_build.fortune.image_ref,
    google_compute_instance.gateway.instance_id,
    google_compute_instance.orchestrator.instance_id,
    google_compute_instance_template.agent.id,
    filesha256("${path.module}/scripts/deploy-fortune.sh"),
    filesha256("${path.module}/scripts/ssh-client.sh"),
    var.demo_user,
    var.demo_app,
    var.demo_tier,
    var.demo_strategy,
  ]

  lifecycle {
    precondition {
      condition     = length(var.ssh_client_cidrs) > 0
      error_message = "enable_demo_bootstrap requires ssh_client_cidrs to allow the Terraform runner."
    }
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
      DEMO_KEY_PEM    = tls_private_key.demo[0].private_key_openssh
      HOST_PUB        = tls_private_key.gateway_host.public_key_openssh
      DEPLOY_USER     = var.demo_user
      DEPLOY_APP      = var.demo_app
      DEPLOY_TIER     = var.demo_tier
      DEPLOY_STRATEGY = var.demo_strategy
    }
    command = <<-EOT
      bash "${path.module}/scripts/deploy-fortune.sh" \
        "${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}" \
        "${ko_build.fortune.image_ref}"
    EOT
  }
}

# Keep release verification separate from deployment: a successful deploy is
# not enough unless the public gateway can certificate-hop into the app and
# return the expected response with both SSH host keys pinned.
resource "terraform_data" "smoke_test_fortune" {
  count = var.enable_demo_bootstrap ? 1 : 0

  triggers_replace = [
    terraform_data.deploy_fortune[0].id,
    filesha256("${path.module}/scripts/verify-fortune.sh"),
    filesha256("${path.module}/scripts/ssh-client.sh"),
    var.demo_user,
    var.demo_app,
  ]

  depends_on = [terraform_data.deploy_fortune]

  provisioner "local-exec" {
    interpreter = ["bash", "-c"]
    environment = {
      DEMO_KEY_PEM = tls_private_key.demo[0].private_key_openssh
      HOST_PUB     = tls_private_key.gateway_host.public_key_openssh
      VERIFY_USER  = var.demo_user
    }
    command = <<-EOT
      bash "${path.module}/scripts/verify-fortune.sh" \
        "${google_compute_instance.gateway.network_interface[0].access_config[0].nat_ip}" \
        "${var.demo_app}"
    EOT
  }
}

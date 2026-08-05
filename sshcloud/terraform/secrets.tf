# Host key + user CA are generated in Terraform for the first environment.
# Private material lands in Terraform state — acceptable for playground / v1;
# rotate via taint + Secret Manager before any serious public deploy.

resource "tls_private_key" "gateway_host" {
  algorithm = "ED25519"
}

resource "tls_private_key" "user_ca" {
  algorithm = "ED25519"
}

# Interim service-to-service bearer tokens. These are separate trust domains:
# gateway → orchestrator and orchestrator → agents. Replace with workload
# identity + mTLS before a public launch.
resource "tls_private_key" "orchestrator_auth" {
  algorithm = "ED25519"
}

resource "tls_private_key" "agent_auth" {
  algorithm = "ED25519"
}

locals {
  demo_ssh_public_keys = [
    for key in tls_private_key.demo : trimspace(key.public_key_openssh)
  ]
  access_member_ssh_public_keys = distinct(concat(
    [for key in var.member_ssh_public_keys : trimspace(key)],
    local.demo_ssh_public_keys,
  ))
  access_deployer_ssh_public_keys = distinct(concat(
    [for key in var.deployer_ssh_public_keys : trimspace(key)],
    local.demo_ssh_public_keys,
  ))
  access_policy_json = jsonencode({
    version                  = 1
    join_mode                = var.access_join_mode
    deploy_mode              = var.access_deploy_mode
    member_ssh_public_keys   = local.access_member_ssh_public_keys
    deployer_ssh_public_keys = local.access_deployer_ssh_public_keys
  })
}

resource "google_secret_manager_secret" "access_policy" {
  secret_id = "${local.prefix}-access-policy"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

# This policy contains public keys only. Secret Manager provides versioned,
# atomic distribution and the same narrow gateway IAM path as private config.
resource "google_secret_manager_secret_version" "access_policy" {
  secret      = google_secret_manager_secret.access_policy.id
  secret_data = local.access_policy_json
}

resource "google_secret_manager_secret" "gateway_host_key" {
  secret_id = "${local.prefix}-gateway-host-key"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "gateway_host_key" {
  secret      = google_secret_manager_secret.gateway_host_key.id
  secret_data = tls_private_key.gateway_host.private_key_openssh
}

resource "google_secret_manager_secret" "user_ca" {
  secret_id = "${local.prefix}-user-ca"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "user_ca" {
  secret      = google_secret_manager_secret.user_ca.id
  secret_data = tls_private_key.user_ca.private_key_openssh
}

resource "google_secret_manager_secret" "user_ca_pub" {
  secret_id = "${local.prefix}-user-ca-pub"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "user_ca_pub" {
  secret      = google_secret_manager_secret.user_ca_pub.id
  secret_data = tls_private_key.user_ca.public_key_openssh
}

resource "google_secret_manager_secret" "orchestrator_auth" {
  secret_id = "${local.prefix}-orchestrator-auth"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "orchestrator_auth" {
  secret      = google_secret_manager_secret.orchestrator_auth.id
  secret_data = sha256(tls_private_key.orchestrator_auth.private_key_openssh)
}

resource "google_secret_manager_secret" "agent_auth" {
  secret_id = "${local.prefix}-agent-auth"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "agent_auth" {
  secret      = google_secret_manager_secret.agent_auth.id
  secret_data = sha256(tls_private_key.agent_auth.private_key_openssh)
}

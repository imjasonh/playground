# Private-environment keys are generated in Terraform and published to Secret
# Manager. Terraform state therefore contains the gateway SSH host private key,
# the platform SSH user-CA private key, both control-CA private keys, every
# control-role leaf private key, and the optional demo private key. Secret
# Manager is distribution, not external key management, and does not remove
# those values from state. The SSH host/user CA below is intentionally separate
# from the HTTPS control PKI.
#
# Rotation epochs make planned replacement deterministic without taint. They do
# not schedule rotation: operators must follow docs/key-rotation-runbook.md,
# inspect the saved plan, retain overlap, and verify each stage.

locals {
  control_ca_generations = {
    for slot, epoch in var.control_ca_rotation_epochs :
    "${slot}-${epoch}" => slot
  }
  control_leaf_generations = {
    for role, epoch in var.control_leaf_rotation_epochs :
    "${role}-${epoch}" => role
  }
}

resource "tls_private_key" "gateway_host" {
  for_each  = toset([tostring(var.gateway_host_key_rotation_epoch)])
  algorithm = "ED25519"

  lifecycle {
    create_before_destroy = true
  }
}

moved {
  from = tls_private_key.gateway_host
  to   = tls_private_key.gateway_host["0"]
}

resource "tls_private_key" "user_ca" {
  algorithm = "ED25519"
}

locals {
  control_roles = toset(["gateway", "orchestrator", "agent", "snapshot"])
  control_role_uris = {
    gateway      = "spiffe://sshcloud.internal/control/gateway"
    orchestrator = "spiffe://sshcloud.internal/control/orchestrator"
    agent        = "spiffe://sshcloud.internal/control/agent"
    snapshot     = "spiffe://sshcloud.internal/control/snapshot"
  }
  control_role_dns = {
    gateway      = "gateway.control.sshcloud.internal"
    orchestrator = "orchestrator.control.sshcloud.internal"
    agent        = "agent.control.sshcloud.internal"
    snapshot     = "snapshot.control.sshcloud.internal"
  }
}

resource "tls_private_key" "control_ca" {
  for_each    = local.control_ca_generations
  algorithm   = "ECDSA"
  ecdsa_curve = "P256"

  lifecycle {
    create_before_destroy = true
  }
}

moved {
  from = tls_private_key.control_ca["a"]
  to   = tls_private_key.control_ca["a-0"]
}

moved {
  from = tls_private_key.control_ca["b"]
  to   = tls_private_key.control_ca["b-0"]
}

locals {
  control_ca_keys = {
    for slot, epoch in var.control_ca_rotation_epochs :
    slot => tls_private_key.control_ca["${slot}-${epoch}"]
  }
}

resource "tls_self_signed_cert" "control_ca" {
  for_each = toset(["a", "b"])

  private_key_pem       = local.control_ca_keys[each.key].private_key_pem
  is_ca_certificate     = true
  validity_period_hours = 43800
  early_renewal_hours   = 0
  allowed_uses          = ["cert_signing", "crl_signing", "digital_signature"]

  subject {
    common_name  = "${local.prefix}-control-ca-${each.key}"
    organization = "sshcloud private control plane"
  }
}

locals {
  control_active_ca_key  = local.control_ca_keys[var.control_ca_active_slot].private_key_pem
  control_active_ca_cert = tls_self_signed_cert.control_ca[var.control_ca_active_slot].cert_pem
}

resource "tls_private_key" "control_role" {
  for_each    = local.control_leaf_generations
  algorithm   = "ECDSA"
  ecdsa_curve = "P256"

  lifecycle {
    create_before_destroy = true
  }
}

moved {
  from = tls_private_key.control_role["gateway"]
  to   = tls_private_key.control_role["gateway-0"]
}

moved {
  from = tls_private_key.control_role["orchestrator"]
  to   = tls_private_key.control_role["orchestrator-0"]
}

moved {
  from = tls_private_key.control_role["agent"]
  to   = tls_private_key.control_role["agent-0"]
}

moved {
  from = tls_private_key.control_role["snapshot"]
  to   = tls_private_key.control_role["snapshot-0"]
}

locals {
  control_role_keys = {
    for role, epoch in var.control_leaf_rotation_epochs :
    role => tls_private_key.control_role["${role}-${epoch}"]
  }
}

resource "tls_cert_request" "control_role" {
  for_each = local.control_roles

  private_key_pem = local.control_role_keys[each.key].private_key_pem
  uris            = [local.control_role_uris[each.key]]
  dns_names       = [local.control_role_dns[each.key]]

  subject {
    common_name  = "sshcloud-control-${each.key}"
    organization = "sshcloud private control plane"
  }
}

resource "tls_locally_signed_cert" "control_role" {
  for_each = local.control_roles

  cert_request_pem      = tls_cert_request.control_role[each.key].cert_request_pem
  ca_private_key_pem    = local.control_active_ca_key
  ca_cert_pem           = local.control_active_ca_cert
  validity_period_hours = 2160
  early_renewal_hours   = 0
  allowed_uses          = ["digital_signature", "client_auth", "server_auth"]
}

resource "google_secret_manager_secret" "control_ca" {
  for_each  = toset(["a", "b"])
  secret_id = "${local.prefix}-control-ca-${each.key}"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "control_ca" {
  for_each    = toset(["a", "b"])
  secret      = google_secret_manager_secret.control_ca[each.key].id
  secret_data = tls_self_signed_cert.control_ca[each.key].cert_pem

  # Superseded trust anchors remain available for explicit rollback/cleanup.
  # The runbook disables and later destroys versions only after proving that
  # no leaf still chains to them.
  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
}

resource "google_secret_manager_secret" "control_identity" {
  for_each  = local.control_roles
  secret_id = "${local.prefix}-control-identity-${each.key}"
  labels    = local.labels
  replication {
    auto {}
  }
  depends_on = [module.project_services]
}

resource "google_secret_manager_secret_version" "control_identity" {
  for_each = local.control_roles
  secret   = google_secret_manager_secret.control_identity[each.key].id
  secret_data = jsonencode({
    certificate_pem = tls_locally_signed_cert.control_role[each.key].cert_pem
    private_key_pem = local.control_role_keys[each.key].private_key_pem
    uri_identity    = local.control_role_uris[each.key]
  })

  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
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

  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
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
  secret_data = tls_private_key.gateway_host[tostring(var.gateway_host_key_rotation_epoch)].private_key_openssh

  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
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

  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
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

  deletion_policy = "ABANDON"

  lifecycle {
    create_before_destroy = true
  }
}

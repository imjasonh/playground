resource "google_service_account" "gateway" {
  account_id   = "${local.prefix}-gateway"
  display_name = "sshcloud SSH gateway"
  depends_on   = [module.project_services]
}

resource "google_service_account" "orchestrator" {
  account_id   = "${local.prefix}-orchestrator"
  display_name = "sshcloud orchestrator"
  depends_on   = [module.project_services]
}

resource "google_service_account" "agent" {
  account_id   = "${local.prefix}-agent"
  display_name = "sshcloud host agent"
  depends_on   = [module.project_services]
}

resource "google_service_account" "snapshot" {
  account_id   = "${local.prefix}-snapshot"
  display_name = "sshcloud snapshot service"
  depends_on   = [module.project_services]
}

locals {
  observability_service_accounts = {
    gateway      = google_service_account.gateway.email
    orchestrator = google_service_account.orchestrator.email
    agent        = google_service_account.agent.email
    snapshot     = google_service_account.snapshot.email
  }
  observability_roles = toset([
    "roles/logging.logWriter",
    "roles/monitoring.metricWriter",
  ])
  observability_grants = {
    for grant in setproduct(keys(local.observability_service_accounts), local.observability_roles) :
    "${grant[0]}-${replace(grant[1], "/", "-")}" => {
      service = grant[0]
      role    = grant[1]
    }
  }
}

# Ops Agent workloads receive only the actively used logging/metrics writer
# roles. No guest receives a service-account token or these credentials.
resource "google_project_iam_member" "observability_writers" {
  for_each = local.observability_grants
  project  = var.project_id
  role     = each.value.role
  member   = "serviceAccount:${local.observability_service_accounts[each.value.service]}"
}

# Gateway: Firestore users/apps + secrets + talk to orchestrator (network only).
resource "google_project_iam_member" "gateway_datastore" {
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${google_service_account.gateway.email}"
  condition {
    title       = "${local.prefix}-gateway-firestore-database"
    description = "Limit gateway data access to the user/app/quota database"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.user_firestore_database}\""
  }
}

resource "google_secret_manager_secret_iam_member" "gateway_host_key" {
  project   = var.project_id
  secret_id = google_secret_manager_secret.gateway_host_key.secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${google_service_account.gateway.email}"
}

resource "google_secret_manager_secret_iam_member" "gateway_user_ca" {
  project   = var.project_id
  secret_id = google_secret_manager_secret.user_ca.secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${google_service_account.gateway.email}"
}

resource "google_secret_manager_secret_iam_member" "gateway_access_policy" {
  project   = var.project_id
  secret_id = google_secret_manager_secret.access_policy.secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${google_service_account.gateway.email}"
}

# Orchestrator: placement journals plus quota counters in separately fenced
# databases, and list MIG members + agent subnet.
resource "google_project_iam_member" "orchestrator_placement_datastore" {
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${google_service_account.orchestrator.email}"
  condition {
    title       = "${local.prefix}-orchestrator-placement-firestore"
    description = "Limit orchestrator placement access to the placement database"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.placement_firestore_database}\""
  }
}

resource "google_project_iam_member" "orchestrator_user_datastore" {
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${google_service_account.orchestrator.email}"
  condition {
    title       = "${local.prefix}-orchestrator-user-firestore"
    description = "Limit orchestrator quota access to the user/app/quota database"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.user_firestore_database}\""
  }
}

resource "google_project_iam_member" "orchestrator_compute_viewer" {
  project = var.project_id
  role    = "roles/compute.viewer"
  member  = "serviceAccount:${google_service_account.orchestrator.email}"
}

# Agent: platform assets and user CA pub. It intentionally has no snapshot
# bucket or Cloud KMS role; all snapshot bytes go through snapshotd.
resource "google_storage_bucket_iam_member" "agent_assets" {
  bucket = google_storage_bucket.assets.name
  role   = "roles/storage.objectViewer"
  member = "serviceAccount:${google_service_account.agent.email}"
}

resource "google_secret_manager_secret_iam_member" "agent_user_ca_pub" {
  project   = var.project_id
  secret_id = google_secret_manager_secret.user_ca_pub.secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${google_service_account.agent.email}"
}

resource "google_project_iam_member" "snapshot_datastore" {
  project = var.project_id
  role    = "roles/datastore.viewer"
  member  = "serviceAccount:${google_service_account.snapshot.email}"
  condition {
    title       = "${local.prefix}-snapshot-firestore-database"
    description = "Limit snapshotd to read-only placement records"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.placement_firestore_database}\""
  }
}

resource "google_storage_bucket_iam_member" "snapshot_objects" {
  bucket = google_storage_bucket.snapshots.name
  role   = "roles/storage.objectAdmin"
  member = "serviceAccount:${google_service_account.snapshot.email}"
}

resource "google_kms_crypto_key_iam_member" "snapshot_kek" {
  crypto_key_id = google_kms_crypto_key.snapshot_envelope.id
  role          = "roles/cloudkms.cryptoKeyEncrypterDecrypter"
  member        = "serviceAccount:${google_service_account.snapshot.email}"
}

locals {
  control_service_accounts = {
    gateway      = google_service_account.gateway.email
    orchestrator = google_service_account.orchestrator.email
    agent        = google_service_account.agent.email
    snapshot     = google_service_account.snapshot.email
  }
  control_ca_grants = {
    for pair in setproduct(local.control_roles, toset(["a", "b"])) :
    "${pair[0]}-${pair[1]}" => {
      role = pair[0]
      slot = pair[1]
    }
  }
}

resource "google_secret_manager_secret_iam_member" "control_identity" {
  for_each  = local.control_roles
  project   = var.project_id
  secret_id = google_secret_manager_secret.control_identity[each.key].secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${local.control_service_accounts[each.key]}"
}

resource "google_secret_manager_secret_iam_member" "control_ca" {
  for_each  = local.control_ca_grants
  project   = var.project_id
  secret_id = google_secret_manager_secret.control_ca[each.value.slot].secret_id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${local.control_service_accounts[each.value.role]}"
}

resource "google_artifact_registry_repository_iam_member" "pullers" {
  for_each = {
    gateway      = google_service_account.gateway.email
    orchestrator = google_service_account.orchestrator.email
    agent        = google_service_account.agent.email
    snapshot     = google_service_account.snapshot.email
  }
  project    = var.project_id
  location   = var.region
  repository = google_artifact_registry_repository.sshcloud.name
  role       = "roles/artifactregistry.reader"
  member     = "serviceAccount:${each.value}"
}

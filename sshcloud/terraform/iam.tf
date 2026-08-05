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

# Gateway: Firestore users/apps + secrets + talk to orchestrator (network only).
resource "google_project_iam_member" "gateway_datastore" {
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${google_service_account.gateway.email}"
  condition {
    title       = "${local.prefix}-gateway-firestore-database"
    description = "Limit gateway data access to the dedicated sshcloud database"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.firestore_database}\""
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

# Orchestrator: Firestore placement + list MIG members + agent subnet.
resource "google_project_iam_member" "orchestrator_datastore" {
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${google_service_account.orchestrator.email}"
  condition {
    title       = "${local.prefix}-orchestrator-firestore-database"
    description = "Limit orchestrator data access to the dedicated sshcloud database"
    expression  = "resource.name == \"projects/${var.project_id}/databases/${var.firestore_database}\""
  }
}

resource "google_project_iam_member" "orchestrator_compute_viewer" {
  project = var.project_id
  role    = "roles/compute.viewer"
  member  = "serviceAccount:${google_service_account.orchestrator.email}"
}

# Agent: snapshot + asset buckets, user CA pub.
resource "google_storage_bucket_iam_member" "agent_snapshots" {
  bucket = google_storage_bucket.snapshots.name
  role   = "roles/storage.objectAdmin"
  member = "serviceAccount:${google_service_account.agent.email}"
}

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

locals {
  control_service_accounts = {
    gateway      = google_service_account.gateway.email
    orchestrator = google_service_account.orchestrator.email
    agent        = google_service_account.agent.email
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
  }
  project    = var.project_id
  location   = var.region
  repository = google_artifact_registry_repository.sshcloud.name
  role       = "roles/artifactregistry.reader"
  member     = "serviceAccount:${each.value}"
}

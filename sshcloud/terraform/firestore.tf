resource "google_firestore_database" "sshcloud" {
  project     = var.project_id
  name        = var.firestore_database
  location_id = var.firestore_location
  type        = "FIRESTORE_NATIVE"

  depends_on = [module.project_services]
}

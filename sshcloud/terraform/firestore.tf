resource "google_firestore_database" "default" {
  count       = var.manage_firestore_database ? 1 : 0
  project     = var.project_id
  name        = "(default)"
  location_id = var.firestore_location
  type        = "FIRESTORE_NATIVE"

  depends_on = [google_project_service.services]
}

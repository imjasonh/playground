resource "google_firestore_database" "user" {
  project     = var.project_id
  name        = var.user_firestore_database
  location_id = var.firestore_location
  type        = "FIRESTORE_NATIVE"

  depends_on = [module.project_services]
}

resource "google_firestore_database" "placement" {
  project     = var.project_id
  name        = var.placement_firestore_database
  location_id = var.firestore_location
  type        = "FIRESTORE_NATIVE"

  depends_on = [module.project_services]
}

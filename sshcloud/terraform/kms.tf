data "google_storage_project_service_account" "gcs" {
  project    = var.project_id
  depends_on = [module.project_services]
}

resource "google_kms_key_ring" "snapshots" {
  name     = "${local.prefix}-snapshots"
  location = var.region

  depends_on = [module.project_services]
}

resource "google_kms_crypto_key" "snapshot_bucket" {
  name     = "snapshot-bucket"
  key_ring = google_kms_key_ring.snapshots.id
  purpose  = "ENCRYPT_DECRYPT"

  lifecycle {
    prevent_destroy = true
  }
}

resource "google_kms_crypto_key" "snapshot_envelope" {
  name     = "snapshot-envelope"
  key_ring = google_kms_key_ring.snapshots.id
  purpose  = "ENCRYPT_DECRYPT"

  lifecycle {
    prevent_destroy = true
  }
}

# GCS needs the KEK independently to apply the bucket's default CMEK. snapshotd
# receives its own encrypt/decrypt grant for envelope keysets in iam.tf.
resource "google_kms_crypto_key_iam_member" "snapshot_bucket_cmek" {
  crypto_key_id = google_kms_crypto_key.snapshot_bucket.id
  role          = "roles/cloudkms.cryptoKeyEncrypterDecrypter"
  member        = "serviceAccount:${data.google_storage_project_service_account.gcs.email_address}"
}

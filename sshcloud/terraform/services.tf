locals {
  required_services = toset([
    "artifactregistry.googleapis.com",
    "cloudresourcemanager.googleapis.com",
    "cloudkms.googleapis.com",
    "compute.googleapis.com",
    "firestore.googleapis.com",
    "iam.googleapis.com",
    "iamcredentials.googleapis.com",
    "iap.googleapis.com",
    "secretmanager.googleapis.com",
    "serviceusage.googleapis.com",
    "storage.googleapis.com",
  ])
}

// Keep API bootstrap in a small module so every API-backed foundation can
// depend on one graph node. In particular, this defers provider data reads
// until apply when a project starts with its APIs disabled.
module "project_services" {
  source = "./modules/project-services"

  project_id = var.project_id
  services   = local.required_services
}

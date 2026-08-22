locals {
  network_name = "${var.name}-vpc"
  subnet_name  = "${var.name}-subnet"
  cluster_name = "${var.name}-autopilot"
  ar_repo_id   = "${var.name}-apps"

  pods_range_name     = "pods"
  services_range_name = "services"

  ssh_source_ranges = length(var.ssh_allowed_cidrs) > 0 ? var.ssh_allowed_cidrs : ["0.0.0.0/0"]

  dns_zone_name = var.create_dns_zone ? google_dns_managed_zone.apps[0].name : data.google_dns_managed_zone.existing[0].name
}

resource "google_project_service" "services" {
  for_each = toset([
    "artifactregistry.googleapis.com",
    "compute.googleapis.com",
    "container.googleapis.com",
    "dns.googleapis.com",
    "iam.googleapis.com",
    "iamcredentials.googleapis.com",
    "cloudresourcemanager.googleapis.com",
    "sts.googleapis.com",
  ])

  project            = var.project_id
  service            = each.key
  disable_on_destroy = false
}

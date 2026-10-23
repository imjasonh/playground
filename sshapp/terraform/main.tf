locals {
  network_name = "${var.name}-vpc"
  subnet_name  = "${var.name}-subnet"
  cluster_name = "${var.name}-autopilot"
  ar_repo_id   = "${var.name}-apps"

  pods_range_name     = "pods"
  services_range_name = "services"

  ssh_source_ranges = length(var.ssh_allowed_cidrs) > 0 ? var.ssh_allowed_cidrs : ["0.0.0.0/0"]

  # Cloud DNS is optional. An empty domain skips the zone and records, so
  # the GitHub Actions deploy can apply with only project_id and reach the
  # mux by its LoadBalancer IP. Set a domain to publish ssh.<domain>.
  manage_dns        = var.domain != ""
  create_dns_zone   = local.manage_dns && var.create_dns_zone
  use_existing_zone = local.manage_dns && !var.create_dns_zone

  dns_zone_name = local.create_dns_zone ? google_dns_managed_zone.apps[0].name : (
    local.use_existing_zone ? data.google_dns_managed_zone.existing[0].name : ""
  )

  mux_load_balancer_ip = one([
    for ingress in kubernetes_service_v1.mux.status[0].load_balancer[0].ingress : ingress.ip
    if ingress.ip != null && ingress.ip != ""
  ])
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

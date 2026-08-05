resource "google_compute_network" "sshcloud" {
  name                    = local.prefix
  auto_create_subnetworks = false
  depends_on              = [module.project_services]
}

resource "google_compute_subnetwork" "sshcloud" {
  name                     = local.prefix
  ip_cidr_range            = "10.20.0.0/20"
  region                   = var.region
  network                  = google_compute_network.sshcloud.id
  private_ip_google_access = true
}

resource "google_compute_router" "sshcloud" {
  name    = local.prefix
  region  = var.region
  network = google_compute_network.sshcloud.id
}

resource "google_compute_router_nat" "sshcloud" {
  name                               = local.prefix
  router                             = google_compute_router.sshcloud.name
  region                             = var.region
  nat_ip_allocate_option             = "AUTO_ONLY"
  source_subnetwork_ip_ranges_to_nat = "LIST_OF_SUBNETWORKS"

  subnetwork {
    name                    = google_compute_subnetwork.sshcloud.id
    source_ip_ranges_to_nat = ["ALL_IP_RANGES"]
  }
}

resource "google_compute_firewall" "gateway_ssh" {
  count   = length(var.ssh_client_cidrs) > 0 ? 1 : 0
  name    = "${local.prefix}-gateway-ssh"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["22"]
  }

  source_ranges = var.ssh_client_cidrs
  target_tags   = ["${local.prefix}-gateway"]
}

resource "google_compute_firewall" "iap_ssh" {
  name    = "${local.prefix}-iap-ssh"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["22", "2222"]
  }

  source_ranges = ["35.235.240.0/20"]
  target_tags   = ["${local.prefix}-gateway", "${local.prefix}-orchestrator", "${local.prefix}-agent", "${local.prefix}-snapshot"]
}

# Host sshd is moved to 2222 on the gateway (app SSH takes :22).

resource "google_compute_firewall" "gateway_to_orchestrator" {
  name    = "${local.prefix}-gateway-to-orchestrator"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8090"]
  }

  source_tags = ["${local.prefix}-gateway"]
  target_tags = ["${local.prefix}-orchestrator"]
}

# These ports carry TLS 1.3 mTLS. Source tags are defense in depth; the API
# still requires exact role URI and GCE workload-token claims.
resource "google_compute_firewall" "orchestrator_to_gateway" {
  name    = "${local.prefix}-orchestrator-to-gateway"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8079"]
  }

  source_tags = ["${local.prefix}-orchestrator"]
  target_tags = ["${local.prefix}-gateway"]
}

resource "google_compute_firewall" "orchestrator_to_agents" {
  name    = "${local.prefix}-orchestrator-to-agents"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8080", "8081"]
  }

  source_tags = ["${local.prefix}-orchestrator"]
  target_tags = ["${local.prefix}-agent"]
}

resource "google_compute_firewall" "gateway_to_agent_relays" {
  name    = "${local.prefix}-gateway-to-agent-relays"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["20000-29999"]
  }

  source_tags = ["${local.prefix}-gateway"]
  target_tags = ["${local.prefix}-agent"]
}

resource "google_compute_firewall" "agents_to_snapshot" {
  name    = "${local.prefix}-agents-to-snapshot"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8082"]
  }

  source_tags = ["${local.prefix}-agent"]
  target_tags = ["${local.prefix}-snapshot"]
}

resource "google_compute_firewall" "orchestrator_to_snapshot_health" {
  name    = "${local.prefix}-orchestrator-to-snapshot-health"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8083"]
  }

  source_tags = ["${local.prefix}-orchestrator"]
  target_tags = ["${local.prefix}-snapshot"]
}

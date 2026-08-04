resource "google_compute_network" "sshcloud" {
  name                    = local.prefix
  auto_create_subnetworks = false
  depends_on              = [google_project_service.services]
}

resource "google_compute_subnetwork" "sshcloud" {
  name          = local.prefix
  ip_cidr_range = "10.20.0.0/20"
  region        = var.region
  network       = google_compute_network.sshcloud.id
}

resource "google_compute_firewall" "gateway_ssh" {
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
  target_tags   = ["${local.prefix}-gateway", "${local.prefix}-orchestrator", "${local.prefix}-agent"]
}

# Host sshd is moved to 2222 on the gateway (app SSH takes :22).

resource "google_compute_firewall" "internal" {
  name    = "${local.prefix}-internal"
  network = google_compute_network.sshcloud.name

  allow {
    protocol = "tcp"
    ports    = ["8080", "8090"]
  }

  source_ranges = [google_compute_subnetwork.sshcloud.ip_cidr_range]
  target_tags   = ["${local.prefix}-orchestrator", "${local.prefix}-agent"]
}

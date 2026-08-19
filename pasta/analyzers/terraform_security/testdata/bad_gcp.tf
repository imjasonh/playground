resource "google_compute_firewall" "ssh" { # want "allows SSH (22) from 0.0.0.0/0"
  source_ranges = ["0.0.0.0/0"]

  allow {
    protocol = "tcp"
    ports    = ["22"]
  }
}

resource "google_container_cluster" "legacy" { # want "enables legacy ABAC"
  enable_legacy_abac = true
}

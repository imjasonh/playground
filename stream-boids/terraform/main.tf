# stream-boids runs on one Spot VM in a regional managed instance group.
# When Google preempts the VM, it stops, the group starts it again once
# its zone has capacity, and it picks the stream up again. YouTube keeps
# the broadcast live across the gap when the broadcast was scheduled with
# Auto-start on and Auto-stop off.
#
# The stream key and YouTube API key live in Secret Manager. This stack
# creates the two secrets without versions: add each value with gcloud,
# so it never enters Terraform state, a plan, or the VM's metadata. Only
# the VM's service account can read the values.
#
# The VM has no inbound firewall rules, OS Login is required, and project
# SSH keys are blocked. Logs go to Cloud Logging.

resource "google_project_service" "services" {
  for_each = toset([
    "artifactregistry.googleapis.com",
    "compute.googleapis.com",
    "logging.googleapis.com",
    "secretmanager.googleapis.com",
    # The API key in Secret Manager calls the YouTube Data API, which must
    # be enabled in the key's project.
    "youtube.googleapis.com",
  ])

  service            = each.key
  disable_on_destroy = false
}

resource "google_artifact_registry_repository" "images" {
  repository_id = var.name
  location      = var.region
  format        = "DOCKER"

  depends_on = [google_project_service.services]
}

data "apko_config" "base" {
  config_contents = file("${path.module}/../apko.yaml")
}

resource "apko_build" "base" {
  repo    = "${local.registry}/base"
  config  = data.apko_config.base.config
  configs = data.apko_config.base.configs
}

resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/stream-boids"
  working_dir = abspath("${path.module}/..")
  base_image  = apko_build.base.image_ref
  platforms   = ["linux/amd64", "linux/arm64"]
  sbom        = "none"
  # Go otherwise stamps the commit into the binary, so every merge to main
  # changes the digest, which replaces the template and restarts the VM.
  env = ["GOFLAGS=-buildvcs=false"]
}

import {
  to = google_service_account.vm
  id = "projects/${var.project_id}/serviceAccounts/${var.name}@${var.project_id}.iam.gserviceaccount.com"
}

resource "google_service_account" "vm" {
  account_id   = var.name
  display_name = "stream-boids VM"
}

resource "google_project_iam_member" "vm_logging" {
  project = var.project_id
  role    = "roles/logging.logWriter"
  member  = "serviceAccount:${google_service_account.vm.email}"
}

resource "google_artifact_registry_repository_iam_member" "vm_pull" {
  repository = google_artifact_registry_repository.images.name
  location   = google_artifact_registry_repository.images.location
  role       = "roles/artifactregistry.reader"
  member     = "serviceAccount:${google_service_account.vm.email}"
}

# Each secret's ID is what the service asks for by name.
locals {
  secrets = toset(["stream-key", "youtube-api-key"])
}

resource "google_secret_manager_secret" "secrets" {
  for_each = local.secrets

  secret_id = each.key
  replication {
    auto {}
  }

  depends_on = [google_project_service.services]
}

resource "google_secret_manager_secret_iam_member" "vm" {
  for_each = local.secrets

  secret_id = google_secret_manager_secret.secrets[each.key].id
  role      = "roles/secretmanager.secretAccessor"
  member    = "serviceAccount:${google_service_account.vm.email}"
}

# A network of its own, with no firewall rules, so nothing can connect in.
# Egress to YouTube goes through the VM's ephemeral external address.
resource "google_compute_network" "net" {
  name                    = var.name
  auto_create_subnetworks = false

  depends_on = [google_project_service.services]
}

resource "google_compute_subnetwork" "net" {
  name          = var.name
  network       = google_compute_network.net.id
  region        = var.region
  ip_cidr_range = "10.10.0.0/24"
}

locals {
  env = {
    STREAM_KEY_SECRET      = google_secret_manager_secret.secrets["stream-key"].secret_id
    YOUTUBE_API_KEY_SECRET = google_secret_manager_secret.secrets["youtube-api-key"].secret_id
    CHANNEL_ID             = var.channel_id
    VIDEO_ID               = var.video_id
    WIDTH                  = tostring(var.width)
    HEIGHT                 = tostring(var.height)
    FPS                    = tostring(var.fps)
    BOID_CAP               = tostring(var.boid_cap)
    X264_PRESET            = var.x264_preset
    VIDEO_BITRATE          = tostring(var.video_bitrate)
    LOG_LEVEL              = var.log_level
  }

  family = split("-", var.machine_type)[0]
  # The image is built for both architectures, so the machine family picks
  # the boot image.
  arm = contains(["t2a", "c4a", "n4a"], local.family)
  # Newer families boot from Hyperdisk, and some support nothing else. The
  # rest need Persistent Disk.
  hyperdisk = contains(["c3", "c3d", "c4", "c4a", "c4d", "n4", "n4a", "n4d"], local.family)
}

resource "google_compute_instance_template" "vm" {
  name_prefix  = "${var.name}-"
  machine_type = var.machine_type

  scheduling {
    # A managed instance group refuses Spot VMs that delete themselves.
    instance_termination_action = "STOP"
    provisioning_model          = "SPOT"
    preemptible                 = true
    automatic_restart           = false
    on_host_maintenance         = "TERMINATE"
  }

  disk {
    # The family resolves when each VM is created, so a new COS release
    # doesn't replace the template.
    source_image = local.arm ? "cos-cloud/cos-arm64-stable" : "cos-cloud/cos-stable"
    disk_type    = local.hyperdisk ? "hyperdisk-balanced" : "pd-balanced"
    disk_size_gb = 10
    # Hyperdisk's free baseline. More costs extra and the VM doesn't need it.
    provisioned_iops       = local.hyperdisk ? 3000 : null
    provisioned_throughput = local.hyperdisk ? 140 : null
    auto_delete            = true
    boot                   = true
  }

  network_interface {
    subnetwork = google_compute_subnetwork.net.id
    nic_type   = "GVNIC"
    access_config {}
  }

  service_account {
    email  = google_service_account.vm.email
    scopes = ["cloud-platform"]
  }

  shielded_instance_config {
    enable_secure_boot          = true
    enable_vtpm                 = true
    enable_integrity_monitoring = true
  }

  metadata = {
    enable-oslogin         = "TRUE"
    block-project-ssh-keys = "TRUE"
    google-logging-enabled = "true"
    user-data = templatefile("${path.module}/cloud-init.yaml.tftpl", {
      registry = "${var.region}-docker.pkg.dev"
      image    = ko_build.app.image_ref
      env      = join("\n", [for k, v in local.env : "${k}=${v}"])
    })
  }

  lifecycle {
    create_before_destroy = true
  }

  depends_on = [
    google_project_iam_member.vm_logging,
    google_artifact_registry_repository_iam_member.vm_pull,
    google_secret_manager_secret_iam_member.vm,
  ]
}

resource "google_compute_region_instance_group_manager" "vm" {
  name               = var.name
  region             = var.region
  base_instance_name = var.name
  target_size        = var.running ? 1 : 0

  version {
    instance_template = google_compute_instance_template.vm.id
  }

  # Never surge: two VMs would stream to the same key at once. A new
  # template replaces the VM, and YouTube waits for the stream to return.
  # A regional group needs max_unavailable of 0 or at least its zone count.
  update_policy {
    type                         = "PROACTIVE"
    minimal_action               = "REPLACE"
    instance_redistribution_type = "NONE"
    max_surge_fixed              = 0
    max_unavailable_fixed        = length(data.google_compute_zones.available.names)
    replacement_method           = "RECREATE"
  }
}

data "google_compute_zones" "available" {
  region = var.region

  depends_on = [google_project_service.services]
}

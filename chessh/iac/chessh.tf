# Stable SSH host key for the game server. Kept in Terraform state (R2) so
# clients do not see host-key warnings across deploys.
resource "tls_private_key" "ssh_host" {
  algorithm = "ED25519"
}

resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/chessh"
  working_dir = ".."
  # Exact GHCR repository (no importpath suffix). Keep the package public so
  # exe.dev can pull without registry credentials.
  repo = "ghcr.io/imjasonh/playground/chessh"
  # Rootful static base so the process can bind the SSH port inside the VM.
  base_image = "gcr.io/distroless/static:latest"
  platforms  = ["linux/amd64"]
  sbom       = "none"
}

resource "exedev_vm" "app" {
  name  = "chessh"
  image = ko_build.app.image_ref
  disk  = "10GB"

  env = {
    # PKCS#8 PEM; loadHostKey in main.go reads SSH_HOST_KEY.
    SSH_HOST_KEY = tls_private_key.ssh_host.private_key_pem
    # Optional HTTP health listener (exe.dev HTTPS proxy can target it).
    PORT = "8080"
  }
}

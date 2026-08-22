resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/chessh"
  working_dir = ".."
  # Exact GHCR repository (no importpath suffix). Keep the package public so
  # exe.dev can pull without registry credentials.
  repo = "ghcr.io/imjasonh/playground/chessh"
  # Minimal static base (Chainguard equivalent of distroless/static).
  # Note: cgr.dev/chainguard/latest is not a public image (FORBIDDEN).
  base_image = "cgr.dev/chainguard/static:latest"
  platforms  = ["linux/amd64"]
  sbom       = "none"
}

resource "exedev_vm" "app" {
  name  = "chessh"
  image = ko_build.app.image_ref
  disk  = "10GB"

  env = {
    # Optional HTTP health listener (exe.dev HTTPS proxy can target it).
    PORT = "8080"
  }
}

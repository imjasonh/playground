resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/chessh"
  working_dir = ".."
  # Exact GHCR repository (no importpath suffix). Keep the package public so
  # exe.dev can pull without registry credentials.
  repo = "ghcr.io/imjasonh/playground/chessh"
  # No shell: wish is PID 1 and listens on :22 so exe.dev's SSH edge dials it
  # directly. Must run as root to bind port 22 (Chainguard static is nonroot).
  # chainguard/latest is FORBIDDEN.
  base_image = "gcr.io/distroless/static-debian12"
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

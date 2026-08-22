resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/chessh"
  working_dir = ".."
  # Exact GHCR repository (no importpath suffix). Keep the package public so
  # exe.dev can pull without registry credentials.
  repo = "ghcr.io/imjasonh/playground/chessh"
  # ubuntu so exe.dev's injected sshd has a normal user database. Login shell
  # is set to the chessh binary (not bash) via `command` below.
  # chainguard/latest is FORBIDDEN.
  base_image = "ubuntu:24.04"
  platforms  = ["linux/amd64"]
  sbom       = "none"
}

resource "exedev_vm" "app" {
  name  = "chessh"
  image = ko_build.app.image_ref
  disk  = "10GB"

  env = {
    PORT        = "8080"
    CHESSH_ADDR = "127.0.0.1:2222"
  }

  # exe.dev's edge always SSHs to its injected sshd (not our process on :22).
  # Point the login program at this binary so interactive sessions hop into
  # local wish; PID 1 runs wish serve. Non-interactive `ssh host -c` is
  # handled inside the binary by exec'ing /bin/sh.
  command = <<-EOT
    /bin/bash -c 'BIN=/ko-app/chessh; for u in root ubuntu; do if getent passwd "$u" >/dev/null; then usermod -s "$BIN" "$u"; fi; done; exec "$BIN" serve'
  EOT
}

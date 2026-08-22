resource "ko_build" "app" {
  importpath  = "github.com/imjasonh/playground/chessh"
  working_dir = ".."
  # Exact GHCR repository (no importpath suffix). Keep the package public so
  # exe.dev can pull without registry credentials.
  repo = "ghcr.io/imjasonh/playground/chessh"
  # Need a real shell for exe.dev's injected sshd login hop.
  # static:latest has no /bin/sh. chainguard/latest is FORBIDDEN.
  base_image = "cgr.dev/chainguard/wolfi-base:latest"
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
    # Wish listens here; login shells hop in via `chessh play`.
    CHESSH_ADDR = "127.0.0.1:2222"
  }

  # exe.dev owns port 22 (injected sshd). The container entrypoint runs wish
  # on :2222. Interactive logins source profile.d and exec into the game.
  # Non-interactive `ssh host <cmd>` does not source profile, so probes stay
  # usable.
  setup_script = <<-EOT
    #!/bin/sh
    set -eu
    BIN=/ko-app/chessh
    if [ ! -x "$BIN" ]; then
      BIN="$(readlink -f /proc/1/exe)"
    fi
    mkdir -p /etc/profile.d /root
    printf 'if [ -n "$${SSH_CONNECTION:-}$${SSH_CLIENT:-}" ] && [ -t 0 ]; then\n  exec "%s" play\nfi\n' "$BIN" > /etc/profile.d/chessh.sh
    printf '. /etc/profile.d/chessh.sh\n' > /root/.profile
  EOT
}

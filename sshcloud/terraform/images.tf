resource "ko_build" "gateway" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/gateway"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/gateway"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "orchestrator" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/orchestrator"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/orchestrator"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "agent" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/agent"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/agent"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "snapshot" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/snapshotd"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/snapshotd"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "vmmhelper" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/vmmhelper"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/vmmhelper"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "taphelper" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/taphelper"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/taphelper"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

resource "ko_build" "guestinit" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/guestinit"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/guestinit"
  platforms   = ["linux/amd64"]
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

# Sample SSH app — deploy this digest like any other user app (not a gateway builtin).
resource "ko_build" "fortune" {
  importpath  = "github.com/imjasonh/playground/sshcloud/cmd/fortune"
  working_dir = "${path.module}/.."
  repo        = "${local.registry}/fortune"
  platforms   = ["linux/amd64"]
  base_image  = "scratch"
  sbom        = "spdx"

  depends_on = [google_artifact_registry_repository.sshcloud]
}

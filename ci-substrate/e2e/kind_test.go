// Package e2e runs a KinD end-to-end check of the ci-substrate control plane.
//
// Opt in with CI_SUBSTRATE_KIND_E2E=1 (CI sets this when the ci-substrate
// module changes). Requires Docker, and installs kind/ko/kubectl when missing.
// The script builds every image with ko and applies the manifests with
// `ko apply`; there are no Dockerfiles and no Helm charts.
package e2e_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

func TestKindMultiTenantCache(t *testing.T) {
	if os.Getenv("CI_SUBSTRATE_KIND_E2E") != "1" {
		t.Skip("set CI_SUBSTRATE_KIND_E2E=1 to run the KinD e2e (CI enables this for ci-substrate PRs)")
	}
	if _, err := exec.LookPath("docker"); err != nil {
		t.Skip("docker not available")
	}

	script, err := filepath.Abs("run-kind.sh")
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.CommandContext(t.Context(), "bash", script)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Env = append(os.Environ(), "CI_SUBSTRATE_KIND_E2E=1")
	if err := cmd.Run(); err != nil {
		t.Fatalf("run-kind.sh: %v", err)
	}
}

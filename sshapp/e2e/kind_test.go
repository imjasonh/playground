// Package e2e runs a KinD end-to-end check of the sshapp mux and hello app.
//
// Opt in with SSHAPP_KIND_E2E=1 (CI sets this when the sshapp module changes).
// Requires Docker, kubectl, and network access to install kind/ko if missing.
package e2e_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

func TestKindMuxHello(t *testing.T) {
	if os.Getenv("SSHAPP_KIND_E2E") != "1" {
		t.Skip("set SSHAPP_KIND_E2E=1 to run the KinD e2e (CI enables this for sshapp PRs)")
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
	cmd.Env = append(os.Environ(), "SSHAPP_KIND_E2E=1")
	if err := cmd.Run(); err != nil {
		t.Fatalf("run-kind.sh: %v", err)
	}
}

// Package kind installs the examples in a kind cluster with generate.
//
// Set KUBE_KIND_E2E=1 to run it; CI sets it when kube changes. It needs
// Docker, kubectl, and curl, and installs kind if it's missing.
package kind_test

import (
	"os"
	"os/exec"
	"testing"
)

func TestKind(t *testing.T) {
	if os.Getenv("KUBE_KIND_E2E") != "1" {
		t.Skip("set KUBE_KIND_E2E=1 to install the examples in a kind cluster")
	}
	if _, err := exec.LookPath("docker"); err != nil {
		t.Skip("docker isn't installed")
	}
	cmd := exec.CommandContext(t.Context(), "bash", "run-kind.sh")
	cmd.Stdout, cmd.Stderr = os.Stdout, os.Stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("run-kind.sh: %v", err)
	}
}

// Package kind installs git-k8s and its checks in a kind cluster with
// generate, and checks that branches are fixed, gated, and merged through
// the mirror, which syncs them with a git server outside the cluster.
//
// Set GIT_K8S_KIND_E2E=1 to run it; CI sets it when git-k8s changes. It
// needs Docker, kubectl, git, and curl, and installs kind if it's missing.
package kind_test

import (
	"os"
	"os/exec"
	"testing"
)

func TestKind(t *testing.T) {
	if os.Getenv("GIT_K8S_KIND_E2E") != "1" {
		t.Skip("set GIT_K8S_KIND_E2E=1 to run git-k8s in a kind cluster")
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

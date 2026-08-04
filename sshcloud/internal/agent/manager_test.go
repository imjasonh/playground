package agent

import (
	"context"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
)

func TestEnsureRequiresKVM(t *testing.T) {
	if firecracker.Available() {
		t.Skip("KVM available; this test asserts the no-KVM error path")
	}
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:    dir,
		KernelPath: dir + "/vmlinux",
		BaseRootfs: dir + "/rootfs.ext4",
	})
	if err != nil {
		t.Fatal(err)
	}
	_, err = mgr.Ensure(context.Background(), "alice", "fortune")
	if err == nil || !strings.Contains(err.Error(), "/dev/kvm") {
		t.Fatalf("expected kvm error, got %v", err)
	}
}

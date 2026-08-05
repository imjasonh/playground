package vmmhelper

import (
	"context"
	"errors"
	"net"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"golang.org/x/sys/unix"
)

func testConfig() Config {
	return Config{
		WorkRoot:       "/var/lib/sshcloud/agent",
		ChrootBase:     "/var/lib/sshcloud/jailer",
		Firecracker:    "/var/lib/sshcloud/assets/firecracker",
		Jailer:         "/var/lib/sshcloud/assets/jailer",
		Kernel:         "/var/lib/sshcloud/assets/vmlinux",
		ProxyDir:       "/run/sshcloud/vmm-api",
		CgroupParent:   "sshcloud",
		AgentUID:       991,
		AgentGID:       991,
		ExpectedPeerID: 991,
	}
}

func testLaunchRequest(mode LaunchMode, vcpus, memMiB int64) LaunchRequest {
	identity := observability.RuntimeIdentity{
		User: "alice", App: "fortune", Generation: "g123", RunID: "r0123456789abcdef0123456789abcdef",
	}
	return LaunchRequest{
		VMID: hostisolation.VMIDForInstance("alice", "fortune.g123"),
		Mode: mode, VCPUs: vcpus, MemMiB: memMiB, Identity: identity,
	}
}

func TestJailerArgvIsFixed(t *testing.T) {
	t.Parallel()
	config := testConfig()
	request := testLaunchRequest(LaunchCold, 1, 128)
	uid, err := hostisolation.SandboxID(request.VMID)
	if err != nil {
		t.Fatal(err)
	}
	args, err := JailerArgv(config, request, uid, uid)
	if err != nil {
		t.Fatal(err)
	}
	got := strings.Join(args, "\n")
	want := strings.Join([]string{
		"--id", request.VMID,
		"--exec-file", "/var/lib/sshcloud/assets/firecracker",
		"--uid", uintString(uid),
		"--gid", uintString(uid),
		"--chroot-base-dir", "/var/lib/sshcloud/jailer",
		"--cgroup-version", "2",
		"--parent-cgroup", "sshcloud",
		"--cgroup", "memory.max=536870912",
		"--cgroup", "memory.swap.max=0",
		"--cgroup", "memory.oom.group=1",
		"--cgroup", "cpu.max=100000 100000",
		"--cgroup", "pids.max=64",
		"--resource-limit", "no-file=1024",
		"--resource-limit", "fsize=1207959552",
		"--",
		"--api-sock", "/run/firecracker.socket",
	}, "\n")
	if got != want {
		t.Fatalf("jailer argv:\n%s\nwant:\n%s", got, want)
	}
	for _, forbidden := range []string{"rootfs.ext4", "vm.state", "vm.mem", "iptables", "sudo"} {
		if strings.Contains(got, forbidden) {
			t.Fatalf("jailer argv contains caller/staging value %q", forbidden)
		}
	}
}

func TestLaunchValidationRejectsArbitraryInputs(t *testing.T) {
	t.Parallel()
	tests := []LaunchRequest{
		{VMID: "../escape", Mode: LaunchCold, VCPUs: 1, MemMiB: 128},
		{VMID: "0123abcdef89", Mode: "command", VCPUs: 1, MemMiB: 128},
		{VMID: "0123abcdef89", Mode: LaunchCold, VCPUs: 8, MemMiB: 8192},
	}
	for _, request := range tests {
		if err := request.validate(); err == nil {
			t.Errorf("request %+v passed validation", request)
		}
	}
}

func TestLaunchValidationBindsHostAttributionToVMID(t *testing.T) {
	t.Parallel()
	request := testLaunchRequest(LaunchCold, 1, 128)
	if err := request.validate(); err != nil {
		t.Fatal(err)
	}
	request.Identity.User = "mallory"
	if err := request.validate(); err == nil {
		t.Fatal("mismatched host-side user/app attribution was accepted")
	}
}

func TestJailerArgvRejectsCallerSelectedIdentity(t *testing.T) {
	t.Parallel()
	config := testConfig()
	request := testLaunchRequest(LaunchRestore, 2, 512)
	if _, err := JailerArgv(config, request, 1234, 1234); err == nil {
		t.Fatal("caller-selected UID/GID was accepted")
	}
}

func TestPinnedVersionTokenIsExact(t *testing.T) {
	t.Parallel()
	if !containsWord([]byte("Firecracker v1.10.1\n"), hostisolation.FirecrackerVersion) {
		t.Fatal("exact pinned version was rejected")
	}
	for _, output := range []string{"Firecracker v1.10.10", "Firecracker xv1.10.1", "Firecracker v1.10.1-dev"} {
		if containsWord([]byte(output), hostisolation.FirecrackerVersion) {
			t.Fatalf("non-pinned version output %q was accepted", output)
		}
	}
}

func TestOpenAtBeneathRejectsIntermediateSymlink(t *testing.T) {
	t.Parallel()
	root := t.TempDir()
	outside := t.TempDir()
	if err := os.WriteFile(filepath.Join(outside, "vm.state"), []byte("state"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outside, filepath.Join(root, "snapshot")); err != nil {
		t.Fatal(err)
	}
	rootFD, err := unix.Open(root, unix.O_PATH|unix.O_DIRECTORY|unix.O_CLOEXEC|unix.O_NOFOLLOW, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer unix.Close(rootFD)
	fd, err := openAtBeneath(rootFD, "snapshot/vm.state", unix.O_RDONLY, 0)
	if err == nil {
		_ = unix.Close(fd)
		t.Fatal("intermediate symlink escaped fixed jail root")
	}
}

func TestWaitUnixSocketRejectsWrongPeerUID(t *testing.T) {
	t.Parallel()
	socket := filepath.Join(t.TempDir(), "firecracker.socket")
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()
	accepted := make(chan net.Conn, 1)
	go func() {
		conn, acceptErr := listener.Accept()
		if acceptErr == nil {
			accepted <- conn
		}
	}()
	wrongUID := uint32(os.Getuid()) + 1
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	err = waitUnixSocket(ctx, socket, make(chan struct{}), wrongUID)
	if err == nil || !strings.Contains(err.Error(), "unauthorized peer uid") {
		t.Fatalf("wrong API socket peer UID error = %v", err)
	}
	select {
	case conn := <-accepted:
		_ = conn.Close()
	case <-time.After(time.Second):
		t.Fatal("test API listener did not accept readiness probe")
	}
}

func TestKillFailsWithoutCgroupTerminationProof(t *testing.T) {
	t.Parallel()
	cgroup := t.TempDir()
	if err := os.WriteFile(filepath.Join(cgroup, "cgroup.kill"), nil, 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(cgroup, "cgroup.events"), []byte("populated 1\nfrozen 0\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := killCgroupWithin(cgroup, 0); err == nil || !strings.Contains(err.Error(), "remains populated") {
		t.Fatalf("populated cgroup termination error = %v", err)
	}
}

func TestServerRetainsVMWhenCgroupTerminationFails(t *testing.T) {
	t.Parallel()
	injected := errors.New("cgroup remains populated")
	done := make(chan struct{})
	close(done)
	vmID := "0123abcdef89"
	vm := &managedVM{id: vmID, done: done}
	server := &Server{
		config:          Config{CgroupParent: "sshcloud"},
		vms:             map[string]*managedVM{vmID: vm},
		terminateCgroup: func(string) error { return injected },
	}
	response, err := server.killLocked(vmID)
	if err == nil || !errors.Is(err, injected) {
		t.Fatalf("kill error = %v", err)
	}
	if response.Terminated {
		t.Fatal("failed cgroup termination returned a termination proof")
	}
	if server.vms[vmID] == nil {
		t.Fatal("VM tracking was removed after unconfirmed termination")
	}
}

func uintString(value uint32) string {
	const digits = "0123456789"
	if value == 0 {
		return "0"
	}
	var reversed [10]byte
	i := len(reversed)
	for value > 0 {
		i--
		reversed[i] = digits[value%10]
		value /= 10
	}
	return string(reversed[i:])
}

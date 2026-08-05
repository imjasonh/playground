package vmmhelper

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
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
		SandboxIDBase:  hostisolation.DefaultSandboxIDBase,
		ExpectedPeerID: 991,
	}
}

func TestJailerArgvIsFixed(t *testing.T) {
	t.Parallel()
	config := testConfig()
	request := LaunchRequest{
		VMID: "0123abcdef89", Mode: LaunchCold, VCPUs: 1, MemMiB: 128,
	}
	uid, err := hostisolation.SandboxID(request.VMID, config.SandboxIDBase)
	if err != nil {
		t.Fatal(err)
	}
	args, err := JailerArgv(config, request, uid, uid)
	if err != nil {
		t.Fatal(err)
	}
	got := strings.Join(args, "\n")
	want := strings.Join([]string{
		"--id", "0123abcdef89",
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

func TestJailerArgvRejectsCallerSelectedIdentity(t *testing.T) {
	t.Parallel()
	config := testConfig()
	request := LaunchRequest{
		VMID: "0123abcdef89", Mode: LaunchRestore, VCPUs: 2, MemMiB: 512,
	}
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

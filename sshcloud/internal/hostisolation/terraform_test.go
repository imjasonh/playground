package hostisolation

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestTerraformProductionIsolationStructure(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform")
	startup := readTestFile(t, filepath.Join(root, "scripts", "agent.sh.tftpl"))
	storage := readTestFile(t, filepath.Join(root, "storage.tf"))
	images := readTestFile(t, filepath.Join(root, "images.tf"))
	agents := readTestFile(t, filepath.Join(root, "agents.tf"))

	for _, required := range []string{
		"SocketMode=0600",
		"sshcloud-vmmhelper.service",
		"sshcloud-taphelper.service",
		"User=sshcloud-tap",
		"CapabilityBoundingSet=CAP_NET_ADMIN",
		"-vmm-helper-socket /run/sshcloud/vmmhelper.sock",
		"-tap-helper-socket /run/sshcloud/taphelper.sock",
		"chmod 0660 /dev/kvm",
	} {
		if !strings.Contains(startup, required) {
			t.Errorf("agent startup is missing %q", required)
		}
	}
	for _, forbidden := range []string{
		"chmod 666 /dev/kvm",
		"chmod 0666 /dev/kvm",
		"Environment=SSHCLOUD_IP_DIRECT=1",
	} {
		if strings.Contains(startup, forbidden) {
			t.Errorf("agent startup contains forbidden %q", forbidden)
		}
	}
	agentService := between(startup,
		"cat >/etc/systemd/system/sshcloud-agent.service <<EOF",
		"\nEOF")
	if strings.Contains(agentService, "CAP_NET_ADMIN") ||
		strings.Contains(agentService, "-direct-runtime") ||
		strings.Contains(agentService, "-firecracker") ||
		strings.Contains(agentService, "-kernel") ||
		!strings.Contains(agentService, "DevicePolicy=closed") ||
		!strings.Contains(agentService, "AmbientCapabilities=\n") ||
		!strings.Contains(agentService, "CapabilityBoundingSet=\n") {
		t.Errorf("agent service capability boundary is not empty:\n%s", agentService)
	}
	vmmService := between(startup,
		"cat >/etc/systemd/system/sshcloud-vmmhelper.service <<EOF",
		"\nEOF")
	for _, required := range []string{
		"User=root",
		"-jailer /var/lib/sshcloud/assets/jailer",
		"DeviceAllow=/dev/kvm rwm",
		"Before=sshcloud-agent.service",
	} {
		if !strings.Contains(vmmService, required) {
			t.Errorf("VMM helper service is missing %q:\n%s", required, vmmService)
		}
	}
	if strings.Contains(vmmService, "CAP_NET_ADMIN") {
		t.Errorf("VMM helper service unexpectedly has CAP_NET_ADMIN:\n%s", vmmService)
	}
	tapService := between(startup,
		"cat >/etc/systemd/system/sshcloud-taphelper.service <<EOF",
		"\nEOF")
	for _, required := range []string{
		"User=sshcloud-tap",
		"AmbientCapabilities=CAP_NET_ADMIN",
		"CapabilityBoundingSet=CAP_NET_ADMIN",
		"DeviceAllow=/dev/net/tun rw",
		"RestrictAddressFamilies=AF_UNIX AF_NETLINK AF_INET AF_INET6",
	} {
		if !strings.Contains(tapService, required) {
			t.Errorf("TAP helper service is missing %q:\n%s", required, tapService)
		}
	}
	for _, required := range []string{
		`google_storage_bucket_object" "jailer"`,
		"var.jailer_asset_path",
	} {
		if !strings.Contains(storage, required) {
			t.Errorf("storage.tf is missing %q", required)
		}
	}
	for _, required := range []string{
		`ko_build" "vmmhelper"`,
		`ko_build" "taphelper"`,
	} {
		if !strings.Contains(images, required) {
			t.Errorf("images.tf is missing %q", required)
		}
	}
	for _, required := range []string{"jailer_object", "vmmhelper_image", "taphelper_image"} {
		if !strings.Contains(agents, required) {
			t.Errorf("agents.tf is missing %q", required)
		}
	}
}

func TestTerraformControlPlaneUsesWorkloadIdentityMTLSWithoutBearerSecrets(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform")
	files := []string{
		"secrets.tf", "iam.tf", "gateway.tf", "orchestrator.tf", "agents.tf", "network.tf",
		filepath.Join("scripts", "gateway.sh.tftpl"),
		filepath.Join("scripts", "orchestrator.sh.tftpl"),
		filepath.Join("scripts", "agent.sh.tftpl"),
		filepath.Join("scripts", "run-container.sh.tftpl"),
	}
	var all strings.Builder
	for _, file := range files {
		all.WriteString(readTestFile(t, filepath.Join(root, file)))
	}
	content := all.String()
	for _, forbidden := range []string{
		"control-token-file",
		"agent-token-file",
		"orchestrator_auth",
		"agent_auth",
		"interim bearer",
	} {
		if strings.Contains(content, forbidden) {
			t.Errorf("production Terraform still contains bearer-token artifact %q", forbidden)
		}
	}
	for _, required := range []string{
		"spiffe://sshcloud.internal/control/gateway",
		"spiffe://sshcloud.internal/control/orchestrator",
		"spiffe://sshcloud.internal/control/agent",
		`control_ca["a"]`,
		`control_ca["b"]`,
		"sshcloud-control-identity-refresh.timer",
		"-control-ca-current",
		"-control-ca-previous",
		"-admin-socket /run/sshcloud/orchestrator-admin.sock",
		"https://${orchestrator_ip}:8090",
		"lines.append(f\"{name}=https://{ip}:8080\")",
	} {
		if !strings.Contains(content, required) {
			t.Errorf("production control-plane configuration is missing %q", required)
		}
	}
}

func readTestFile(t *testing.T, path string) string {
	t.Helper()
	content, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(content)
}

func between(content, start, end string) string {
	_, tail, ok := strings.Cut(content, start)
	if !ok {
		return ""
	}
	value, _, _ := strings.Cut(tail, end)
	return value
}

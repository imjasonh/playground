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
		"sandbox-id-base",
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

func TestTerraformBindsHelpersToAgentLifecycle(t *testing.T) {
	t.Parallel()
	startup := readTestFile(t, filepath.Join("..", "..", "terraform", "scripts", "agent.sh.tftpl"))
	for _, helper := range []string{"vmmhelper", "taphelper"} {
		service := between(startup,
			"cat >/etc/systemd/system/sshcloud-"+helper+".service <<EOF",
			"\nEOF")
		for _, required := range []string{
			"BindsTo=sshcloud-agent.service",
			"PartOf=sshcloud-agent.service",
			"Before=sshcloud-agent.service",
			"LimitCORE=0",
		} {
			if !strings.Contains(service, required) {
				t.Errorf("%s helper is not coupled to agent lifecycle by %q:\n%s", helper, required, service)
			}
		}
		if strings.Contains(service, "Restart=") {
			t.Errorf("%s helper can restart independently of agent:\n%s", helper, service)
		}
	}
	agentService := between(startup,
		"cat >/etc/systemd/system/sshcloud-agent.service <<EOF",
		"\nEOF")
	for _, required := range []string{
		"Requires=sshcloud-vmmhelper.service sshcloud-taphelper.service",
		"BindsTo=sshcloud-vmmhelper.service sshcloud-taphelper.service",
		"After=sshcloud-vmmhelper.service sshcloud-taphelper.service",
		"LimitCORE=0",
	} {
		if !strings.Contains(agentService, required) {
			t.Errorf("agent does not require lifecycle-bound helpers via %q:\n%s", required, agentService)
		}
	}
}

func TestTerraformControlPlaneUsesWorkloadIdentityMTLSWithoutBearerSecrets(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform")
	files := []string{
		"secrets.tf", "iam.tf", "gateway.tf", "orchestrator.tf", "snapshotd.tf", "agents.tf", "network.tf",
		filepath.Join("scripts", "gateway.sh.tftpl"),
		filepath.Join("scripts", "orchestrator.sh.tftpl"),
		filepath.Join("scripts", "snapshotd.sh.tftpl"),
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
		"spiffe://sshcloud.internal/control/snapshot",
		`control_ca["a"]`,
		`control_ca["b"]`,
		"sshcloud-control-identity-refresh.timer",
		"-control-bundle /var/lib/sshcloud/control/current",
		"-instance-name $${INSTANCE_NAME}",
		"-instance-id $${INSTANCE_ID}",
		"-gce-zone ${zone}",
		"-agent-service-account ${agent_service_account}",
		"-admin-socket /run/sshcloud/orchestrator-admin.sock",
		"https://${orchestrator_ip}:8090",
		"lines.append(f\"{name}@{instance_id}=https://{ip}:8080\")",
	} {
		if !strings.Contains(content, required) {
			t.Errorf("production control-plane configuration is missing %q", required)
		}
	}
}

func TestTerraformSystemdIsSolePlatformContainerSupervisor(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform", "scripts")
	tests := []struct {
		role        string
		script      string
		requires    []string
		container   string
		imageUnit   string
		serviceUnit string
	}{
		{
			role: "gateway", script: "gateway.sh.tftpl", container: "sshcloud-gateway",
			imageUnit: "sshcloud-gateway-image.service", serviceUnit: "sshcloud-gateway.service",
			requires: []string{
				"docker.service", "sshcloud-control-identity-refresh.service",
				"sshcloud-access-policy-refresh.service", "sshcloud-gateway-image.service",
			},
		},
		{
			role: "orchestrator", script: "orchestrator.sh.tftpl", container: "sshcloud-orchestrator",
			imageUnit: "sshcloud-orchestrator-image.service", serviceUnit: "sshcloud-orchestrator.service",
			requires: []string{
				"docker.service", "sshcloud-control-identity-refresh.service",
				"sshcloud-refresh-hosts.service", "sshcloud-orchestrator-image.service",
			},
		},
		{
			role: "snapshotd", script: "snapshotd.sh.tftpl", container: "sshcloud-snapshotd",
			imageUnit: "sshcloud-snapshotd-image.service", serviceUnit: "sshcloud-snapshotd.service",
			requires: []string{
				"docker.service", "sshcloud-control-identity-refresh.service",
				"sshcloud-snapshotd-image.service",
			},
		},
	}
	for _, tc := range tests {
		tc := tc
		t.Run(tc.role, func(t *testing.T) {
			t.Parallel()
			startup := readTestFile(t, filepath.Join(root, tc.script))
			image := parseSystemdUnit(t, startup, tc.imageUnit)
			service := parseSystemdUnit(t, startup, tc.serviceUnit)

			pull := image.one(t, "Service", "ExecStart")
			if !strings.HasPrefix(pull, "/usr/bin/docker pull ") {
				t.Fatalf("image unit does not pull the pinned input: %q", pull)
			}
			if got := image.one(t, "Service", "Restart"); got != "on-failure" {
				t.Fatalf("image unit restart = %q, want on-failure", got)
			}
			if got := image.one(t, "Service", "LimitCORE"); got != "0" {
				t.Fatalf("image unit LimitCORE = %q", got)
			}

			for _, dependency := range tc.requires {
				if !unitWords(service, "Unit", "Requires")[dependency] {
					t.Errorf("service does not require %s", dependency)
				}
				if !unitWords(service, "Unit", "After")[dependency] {
					t.Errorf("service is not ordered after %s", dependency)
				}
			}
			run := service.one(t, "Service", "ExecStart")
			fields := wordSet(run)
			for _, required := range []string{
				"/usr/bin/docker", "run", "--rm", "--ulimit", "core=0:0",
				"--name", tc.container,
			} {
				if !fields[required] {
					t.Errorf("container command is missing %q: %s", required, run)
				}
			}
			for _, forbidden := range []string{"-d", "--detach"} {
				if fields[forbidden] {
					t.Errorf("container command contains Docker supervision flag %q: %s", forbidden, run)
				}
			}
			for field := range fields {
				if strings.HasPrefix(field, "--restart") {
					t.Errorf("container command contains Docker supervision flag %q: %s", field, run)
				}
			}
			if got := service.one(t, "Service", "Restart"); got != "always" {
				t.Errorf("systemd service Restart = %q, want always", got)
			}
			if got := service.one(t, "Service", "LimitCORE"); got != "0" {
				t.Errorf("systemd service LimitCORE = %q", got)
			}

			disableRestart := "timeout 30s docker update --restart=no " + tc.container
			removeOld := "timeout 30s docker rm -f " + tc.container
			if disableAt, removeAt, unitAt := strings.Index(startup, disableRestart),
				strings.Index(startup, removeOld), strings.Index(startup, "cat >/etc/systemd/system/"+tc.serviceUnit); disableAt < 0 || removeAt < disableAt || unitAt < removeAt {
				t.Errorf("legacy container restart policy is not disabled and removed before installing %s", tc.serviceUnit)
			}
		})
	}
}

func TestTerraformPublishesOneValidatedLeasedControlBundle(t *testing.T) {
	t.Parallel()
	helper := readTestFile(t, filepath.Join("..", "..", "terraform", "scripts", "run-container.sh.tftpl"))
	refresh := between(helper,
		"cat >/usr/local/sbin/sshcloud-refresh-control-identity <<'EOF'",
		"\nEOF")
	for _, required := range []string{
		`flock -n 9`,
		`mktemp -d "$${CONTROL_BUNDLE_ROOT}/.refresh.XXXXXX"`,
		`openssl x509 -in "$tmp/tls.crt"`,
		`openssl pkey -in "$tmp/tls.key"`,
		`openssl dgst -sha256`,
		`test "$uris" = "$CONTROL_EXPECTED_URI"`,
		`for ca in ca-current.pem ca-previous.pem`,
		`openssl verify -purpose sslclient`,
		`openssl verify -purpose sslserver`,
		`test "$verified" -eq 1`,
		`date +%s >"$tmp/validated-at"`,
		`chmod 0750 "$tmp"`,
		`chmod 0640 "$tmp"/*`,
		`mv "$tmp" "$bundle"`,
		`mv -Tf "$link" "$CONTROL_BUNDLE_ROOT/current"`,
	} {
		if !strings.Contains(refresh, required) {
			t.Errorf("atomic control bundle refresh is missing %q", required)
		}
	}
	if !strings.Contains(helper, "CONTROL_OWNER=root") {
		t.Error("control bundles are not root-owned with read-only workload-group access")
	}
	if strings.Index(refresh, `date +%s >"$tmp/validated-at"`) >
		strings.Index(refresh, `mv -Tf "$link" "$CONTROL_BUNDLE_ROOT/current"`) {
		t.Error("control bundle is selected before its validation marker is written")
	}
	check := between(helper,
		"cat >/usr/local/sbin/sshcloud-check-control-bundle <<'EOF'",
		"\nEOF")
	for _, required := range []string{
		`current/validated-at`,
		`age > CONTROL_BUNDLE_LEASE_SECONDS`,
		`last-known-good lease expired`,
	} {
		if !strings.Contains(check, required) {
			t.Errorf("control bundle lease check is missing %q", required)
		}
	}
	refreshUnit := parseSystemdUnit(t, helper, "sshcloud-control-identity-refresh.service")
	exec := refreshUnit.one(t, "Service", "ExecStart")
	if !strings.Contains(exec, "sshcloud-refresh-control-identity || /usr/local/sbin/sshcloud-check-control-bundle") {
		t.Errorf("refresh unit does not use a bounded last-known-good fallback: %s", exec)
	}
	if got := refreshUnit.one(t, "Service", "LimitCORE"); got != "0" {
		t.Errorf("control refresh LimitCORE = %q", got)
	}
	for _, script := range []string{
		"gateway.sh.tftpl", "orchestrator.sh.tftpl", "snapshotd.sh.tftpl", "agent.sh.tftpl",
	} {
		startup := readTestFile(t, filepath.Join("..", "..", "terraform", "scripts", script))
		for _, forbidden := range []string{
			"-control-cert", "-control-key", "-control-ca-current", "-control-ca-previous",
		} {
			if strings.Contains(startup, forbidden) {
				t.Errorf("%s still mounts control identity as independent files via %q", script, forbidden)
			}
		}
	}
}

func TestTerraformRefreshesPolicyAndHostsWithoutPartialPublication(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform", "scripts")
	gateway := readTestFile(t, filepath.Join(root, "gateway.sh.tftpl"))
	if stop, install := strings.Index(gateway, "systemctl stop sshcloud-access-policy-refresh.timer"),
		strings.Index(gateway, "cat >/usr/local/sbin/sshcloud-refresh-access-policy"); stop < 0 || install < stop {
		t.Error("gateway does not stop the prior policy timer before replacing its refresher")
	}
	policy := between(gateway,
		"cat >/usr/local/sbin/sshcloud-refresh-access-policy <<'EOF'",
		"\nEOF")
	for _, required := range []string{
		`flock -n 9`,
		`mktemp "$DEST.tmp.XXXXXX"`,
		`object_pairs_hook=unique_object`,
		`ssh-keygen -l -f "$key_file"`,
		`mv -f "$tmp" "$DEST"`,
	} {
		if !strings.Contains(policy, required) {
			t.Errorf("atomic access-policy refresh is missing %q", required)
		}
	}
	policyCheck := between(gateway,
		"cat >/usr/local/sbin/sshcloud-check-access-policy <<'EOF'",
		"\nEOF")
	if !strings.Contains(policyCheck, "age > 300") ||
		!strings.Contains(policyCheck, "last-known-good lease expired") {
		t.Error("access-policy fallback does not enforce its five-minute lease")
	}
	if got := parseSystemdUnit(t, gateway, "sshcloud-access-policy-refresh.service").
		one(t, "Service", "LimitCORE"); got != "0" {
		t.Errorf("access-policy refresh LimitCORE = %q", got)
	}

	orchestrator := readTestFile(t, filepath.Join(root, "orchestrator.sh.tftpl"))
	if stop, install := strings.Index(orchestrator, "systemctl stop sshcloud-refresh-hosts.timer"),
		strings.Index(orchestrator, "cat >/usr/local/lib/sshcloud/refresh-hosts.py"); stop < 0 || install < stop {
		t.Error("orchestrator does not stop the prior host timer before replacing its refresher")
	}
	hosts := between(orchestrator,
		"cat >/usr/local/lib/sshcloud/refresh-hosts.py <<'PY'",
		"\nPY")
	for _, required := range []string{
		"fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)",
		"tempfile.mkstemp(",
		"os.fsync(output.fileno())",
		"os.replace(tmp, OUT)",
		"if refresh_errors or not lines:",
		"last_known_good",
		"incomplete MIG refresh with no last-known-good host list",
		"urllib.request.urlopen(req, timeout=TIMEOUT)",
	} {
		if !strings.Contains(hosts, required) {
			t.Errorf("atomic host refresh is missing %q", required)
		}
	}
	if got := parseSystemdUnit(t, orchestrator, "sshcloud-refresh-hosts.service").
		one(t, "Service", "LimitCORE"); got != "0" {
		t.Errorf("host refresh LimitCORE = %q", got)
	}
}

func TestTerraformGatewayValidatesSSHDConfigBeforeRestart(t *testing.T) {
	t.Parallel()
	startup := readTestFile(t, filepath.Join("..", "..", "terraform", "scripts", "gateway.sh.tftpl"))
	writeDropIn := strings.Index(startup, "cat >/etc/ssh/sshd_config.d/99-sshcloud-port.conf")
	validate := strings.Index(startup, "/usr/sbin/sshd -t")
	restart := strings.Index(startup, "systemctl restart ssh.service")
	if writeDropIn < 0 || validate < writeDropIn || restart < validate {
		t.Fatal("gateway must write an sshd drop-in, validate the complete config, then restart sshd")
	}
	if strings.Contains(startup, "sed -i") && strings.Contains(startup, "sshd_config") {
		t.Fatal("gateway mutates the base sshd_config instead of using a drop-in")
	}
}

func TestTerraformStartupNetworkCallsHaveDeadlines(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform", "scripts")
	for _, script := range []string{
		"run-container.sh.tftpl", "gateway.sh.tftpl", "orchestrator.sh.tftpl",
		"snapshotd.sh.tftpl", "agent.sh.tftpl",
	} {
		startup := readTestFile(t, filepath.Join(root, script))
		for number, line := range strings.Split(startup, "\n") {
			trimmed := strings.TrimSpace(line)
			isCurlCommand := strings.HasPrefix(trimmed, "curl ") ||
				strings.HasPrefix(trimmed, "if ! curl ") ||
				strings.Contains(trimmed, "$(curl ")
			if !isCurlCommand || strings.Contains(trimmed, "command -v curl") {
				continue
			}
			if !strings.Contains(line, "--connect-timeout") || !strings.Contains(line, "--max-time") {
				t.Errorf("%s:%d has an unbounded curl call: %s", script, number+1, line)
			}
		}
	}

	orchestrator := readTestFile(t, filepath.Join(root, "orchestrator.sh.tftpl"))
	hosts := between(orchestrator,
		"cat >/usr/local/lib/sshcloud/refresh-hosts.py <<'PY'",
		"\nPY")
	if got, want := strings.Count(hosts, "urllib.request.urlopen("), strings.Count(hosts, "timeout="); got != want {
		t.Errorf("host refresh urlopen calls = %d but timeout arguments = %d", got, want)
	}
	for _, startup := range []string{
		readTestFile(t, filepath.Join(root, "run-container.sh.tftpl")),
		readTestFile(t, filepath.Join(root, "agent.sh.tftpl")),
	} {
		if strings.Contains(startup, "retry 10 apt-get") {
			t.Error("startup contains an apt network call without an outer deadline")
		}
	}
}

func TestTerraformSnapshotBoundaryExcludesAgentsFromGCSAndKMS(t *testing.T) {
	t.Parallel()
	root := filepath.Join("..", "..", "terraform")
	iam := readTestFile(t, filepath.Join(root, "iam.tf"))
	storage := readTestFile(t, filepath.Join(root, "storage.tf"))
	kms := readTestFile(t, filepath.Join(root, "kms.tf"))
	agents := readTestFile(t, filepath.Join(root, "agents.tf"))
	agentStartup := readTestFile(t, filepath.Join(root, "scripts", "agent.sh.tftpl"))
	snapshotVM := readTestFile(t, filepath.Join(root, "snapshotd.tf"))
	network := readTestFile(t, filepath.Join(root, "network.tf"))
	images := readTestFile(t, filepath.Join(root, "images.tf"))

	if strings.Contains(iam, "agent_snapshots") || strings.Contains(agentStartup, "-gcs-bucket") {
		t.Fatal("agent retains direct snapshot bucket access")
	}
	for name, content := range map[string]string{
		"storage.tf": storage, "kms.tf": kms, "agents.tf": agents,
		"snapshotd.tf": snapshotVM, "network.tf": network, "images.tf": images,
	} {
		for _, required := range map[string][]string{
			"storage.tf": {"default_kms_key_name"},
			"kms.tf": {
				`google_kms_crypto_key" "snapshot_bucket`,
				`google_kms_crypto_key" "snapshot_envelope`,
				"snapshot_bucket_cmek",
			},
			"agents.tf":    {"snapshotd_url"},
			"snapshotd.tf": {`google_compute_instance" "snapshot`, "kms_key"},
			"network.tf":   {"agents_to_snapshot"},
			"images.tf":    {`ko_build" "snapshot`},
		}[name] {
			if !strings.Contains(content, required) {
				t.Errorf("%s is missing %q", name, required)
			}
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

type testSystemdUnit map[string]map[string][]string

func parseSystemdUnit(t *testing.T, startup, name string) testSystemdUnit {
	t.Helper()
	start := "cat >/etc/systemd/system/" + name + " <<EOF"
	body := between(startup, start, "\nEOF")
	if body == "" {
		start = "cat >/etc/systemd/system/" + name + " <<'EOF'"
		body = between(startup, start, "\nEOF")
	}
	if body == "" {
		t.Fatalf("systemd unit %s was not found", name)
	}

	var logical []string
	pending := ""
	for _, raw := range strings.Split(body, "\n") {
		line := strings.TrimSpace(raw)
		if strings.HasSuffix(line, `\`) {
			pending += strings.TrimSpace(strings.TrimSuffix(line, `\`)) + " "
			continue
		}
		logical = append(logical, strings.TrimSpace(pending+line))
		pending = ""
	}
	if pending != "" {
		logical = append(logical, strings.TrimSpace(pending))
	}

	unit := testSystemdUnit{}
	section := ""
	for _, line := range logical {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if strings.HasPrefix(line, "[") && strings.HasSuffix(line, "]") {
			section = strings.TrimSuffix(strings.TrimPrefix(line, "["), "]")
			if unit[section] == nil {
				unit[section] = map[string][]string{}
			}
			continue
		}
		key, value, ok := strings.Cut(line, "=")
		if !ok || section == "" {
			t.Fatalf("invalid line in systemd unit %s: %q", name, line)
		}
		unit[section][key] = append(unit[section][key], value)
	}
	return unit
}

func (u testSystemdUnit) one(t *testing.T, section, key string) string {
	t.Helper()
	values := u[section][key]
	if len(values) != 1 {
		t.Fatalf("systemd [%s] %s has %d values, want 1: %v", section, key, len(values), values)
	}
	return values[0]
}

func unitWords(unit testSystemdUnit, section, key string) map[string]bool {
	words := map[string]bool{}
	for _, value := range unit[section][key] {
		for word := range wordSet(value) {
			words[word] = true
		}
	}
	return words
}

func wordSet(value string) map[string]bool {
	words := map[string]bool{}
	for _, word := range strings.Fields(value) {
		words[word] = true
	}
	return words
}

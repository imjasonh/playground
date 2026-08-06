package observability

import (
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func terraformSource(t *testing.T, name string) string {
	t.Helper()
	_, current, _, _ := runtime.Caller(0)
	path := filepath.Join(filepath.Dir(current), "..", "..", "terraform", name)
	content, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(content)
}

func TestTerraformObservabilityAPIsIAMAndRetention(t *testing.T) {
	t.Parallel()
	services := terraformSource(t, "services.tf")
	for _, service := range []string{
		`"logging.googleapis.com"`,
		`"monitoring.googleapis.com"`,
	} {
		if !strings.Contains(services, service) {
			t.Errorf("services.tf does not enable %s", service)
		}
	}
	if strings.Contains(services, "cloudtrace.googleapis.com") {
		t.Error("services.tf enables unused Cloud Trace API")
	}

	iam := terraformSource(t, "iam.tf")
	for _, role := range []string{
		`"roles/logging.logWriter"`,
		`"roles/monitoring.metricWriter"`,
	} {
		if strings.Count(iam, role) != 1 {
			t.Errorf("observability IAM role %s count = %d, want 1", role, strings.Count(iam, role))
		}
	}
	for _, forbidden := range []string{"roles/cloudtrace.agent", "roles/logging.bucketWriter"} {
		if strings.Contains(iam, forbidden) {
			t.Errorf("iam.tf retains unused or same-project sink role %q", forbidden)
		}
	}

	config := terraformSource(t, "observability.tf")
	for _, required := range []string{
		`resource "google_logging_project_bucket_config" "platform"`,
		`retention_days = 30`,
		`resource "google_logging_project_bucket_config" "app"`,
		`retention_days = 7`,
		`resource "google_logging_project_sink" "platform"`,
		`AND NOT jsonPayload.log_type=\"app\"`,
		`resource "google_logging_project_sink" "app"`,
		`AND jsonPayload.log_type=\"app\"`,
		`resource "google_logging_log_view" "platform"`,
		`resource "google_logging_log_view" "app"`,
		`resource "google_logging_log_view_iam_member" "platform_readers"`,
		`resource "google_logging_log_view_iam_member" "app_readers"`,
		`role     = "roles/logging.viewAccessor"`,
		`resource "google_logging_project_exclusion" "sshcloud_default"`,
		`count       = var.log_routing_live_verified ? 1 : 0`,
		`metadata.user_labels.\"app\" = \"sshcloud\"`,
		`metadata.user_labels.\"managed\" = \"terraform\"`,
		`resource "google_monitoring_dashboard" "sshcloud"`,
		`resource "google_monitoring_alert_policy" "app_log_drops"`,
		`condition_prometheus_query_language`,
		`increase(sshcloud_app_log_bytes_total{job=~\"sshcloud-(gateway|orchestrator|snapshotd|agent)\",result=\"dropped\"}[5m]) > 0`,
		`resource "google_billing_budget" "monthly"`,
	} {
		if !strings.Contains(config, required) {
			t.Errorf("observability.tf missing %q", required)
		}
	}
	for _, forbidden := range []string{
		`unique_writer_identity`,
		`roles/logging.bucketWriter`,
		`resource "google_project_iam_member" "platform_sink"`,
		`resource "google_project_iam_member" "app_sink"`,
	} {
		if strings.Contains(config, forbidden) {
			t.Errorf("observability.tf retains same-project sink writer configuration %q", forbidden)
		}
	}
}

func TestTerraformInstallsBoundedOpsAgentOnEveryRole(t *testing.T) {
	t.Parallel()
	helper := terraformSource(t, filepath.Join("scripts", "run-container.sh.tftpl"))
	for _, required := range []string{
		"google-cloud-ops-agent",
		"type: systemd_journald",
		"field: MESSAGE",
		"type: prometheus",
		"sample_limit: 256",
		"SystemMaxUse=512M",
		"RuntimeMaxUse=128M",
		"MaxRetentionSec=7day",
		"install_core_dump_policy",
		"ulimit -c 0",
		"kernel.core_pattern = /dev/null",
		"Storage=none",
		"ProcessSizeMax=0",
		`regex: "^(user|user_id|app|app_id|session|session_id|generation|gen|run|run_id)$"`,
	} {
		if !strings.Contains(helper, required) {
			t.Errorf("shared Ops Agent setup missing %q", required)
		}
	}
	for script, invocation := range map[string]string{
		"gateway.sh.tftpl":      "install_ops_agent gateway",
		"orchestrator.sh.tftpl": "install_ops_agent orchestrator",
		"agent.sh.tftpl":        "install_ops_agent agent",
		"snapshotd.sh.tftpl":    "install_ops_agent snapshotd",
	} {
		if content := terraformSource(t, filepath.Join("scripts", script)); !strings.Contains(content, invocation) {
			t.Errorf("%s missing %q", script, invocation)
		}
	}
}

func TestTerraformAddsNoGuestTelemetryNetworkOrCredentials(t *testing.T) {
	t.Parallel()
	network := terraformSource(t, "network.tf")
	for _, forbidden := range []string{"telemetry", "9080", "4317", "4318"} {
		if strings.Contains(strings.ToLower(network), forbidden) {
			t.Fatalf("guest network contains telemetry exception %q", forbidden)
		}
	}
	agentScript := terraformSource(t, filepath.Join("scripts", "agent.sh.tftpl"))
	for _, forbidden := range []string{
		"/rootfs/google-cloud-ops-agent",
		"/rootfs/application_default_credentials",
		"GOOGLE_APPLICATION_CREDENTIALS=/rootfs",
	} {
		if strings.Contains(agentScript, forbidden) {
			t.Fatalf("agent startup injects host observability credential into guest: %q", forbidden)
		}
	}
}

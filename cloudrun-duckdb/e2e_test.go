package main

import (
	"bytes"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/crsim"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fakegcs"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/scenario"
)

// TestCloudRunLifecycle runs the server under the Cloud Run simulator while
// instances crash, scale to zero, and overlap during deploys, and checks
// that no acknowledged write is lost and the replica restores. The replica
// is a fakegcs server with latproxy's latency, so uploads take as long as
// they would in Cloud Storage and overlapping instances really race.
func TestCloudRunLifecycle(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the server and runs it for half a minute")
	}
	dir := t.TempDir()
	bin := filepath.Join(dir, "cloudrun-duckdb")
	args := []string{"build", "-o", bin}
	if raceEnabled {
		args = append(args, "-race")
	}
	build := exec.Command("go", append(args, ".")...)
	build.Stdout, build.Stderr = os.Stderr, os.Stderr
	if err := build.Run(); err != nil {
		t.Fatalf("go build: %v", err)
	}

	logs, err := os.Create(filepath.Join(dir, "instances.log"))
	if err != nil {
		t.Fatal(err)
	}
	defer func() {
		logs.Close()
		if t.Failed() {
			b, _ := os.ReadFile(logs.Name())
			t.Logf("instance logs:\n%s", b)
		}
	}()

	gcs := httptest.NewServer(fakegcs.New(filepath.Join(dir, "gcs"), fakegcs.LatProxy))
	defer gcs.Close()
	sim := crsim.New(t.Context(), crsim.Config{
		Command: []string{bin},
		Env: []string{
			"REPLICA_URL=gs://replica/db?endpoint=" + gcs.URL,
			"SNAPSHOT_MIN_ENTRIES=8",
			"ADMIN_TOKEN=e2e",
		},
		Output: logs,
	})
	srv := httptest.NewServer(sim)
	defer srv.Close()
	defer sim.Close()

	res, err := scenario.Soak(t.Context(), scenario.SoakConfig{
		URL:         srv.URL,
		Sim:         sim,
		Duration:    25 * time.Second,
		Writers:     4,
		Readers:     4,
		CrashEvery:  7 * time.Second,
		ScaleEvery:  5 * time.Second,
		DeployEvery: 9 * time.Second,
		Overlap:     2 * time.Second,
		AdminToken:  "e2e",
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("acked %d writes, %d reads; %d crashes, %d scale-to-zeros, %d deploys, %d instances; statuses %v",
		res.Acked, res.ReadLatency.Count, res.Crashes, res.ScaleToZeros, res.Deploys, len(res.Instances), res.Statuses)
	if res.Acked == 0 {
		t.Fatal("no writes were acknowledged")
	}
	if res.Crashes == 0 || res.Deploys == 0 || res.ScaleToZeros == 0 {
		t.Errorf("chaos did not run: %+v", res)
	}
	for _, v := range res.Violations {
		t.Error(v)
	}
	sim.Close()
	if b, _ := os.ReadFile(logs.Name()); bytes.Contains(b, []byte("WARNING: DATA RACE")) {
		t.Error("an instance reported a data race")
	}
}

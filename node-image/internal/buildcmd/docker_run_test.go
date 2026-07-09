package buildcmd_test

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
	"github.com/imjasonh/playground/node-image/internal/config"
)

// TestDockerRunBuiltImage checks the end-to-end contract:
//
//	docker run --rm $(node-image build -L …)
//
// Skips when Docker is unavailable (common in CI without a daemon).
func TestDockerRunBuiltImage(t *testing.T) {
	if _, err := exec.LookPath("docker"); err != nil {
		t.Skip("docker not on PATH")
	}
	if err := exec.Command("docker", "info").Run(); err != nil {
		t.Skip("docker daemon not available")
	}

	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}

	plat := "linux/amd64"
	if runtime.GOARCH == "arm64" {
		plat = "linux/arm64"
	}

	var stdout, stderr bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		Local:     true,
		Repo:      "pure-js-fixture",
		Base:      config.DefaultBase,
		SkipBuild: true,
		Platforms: []string{plat},
		Tags:      []string{"test"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, stderr.String())
	}

	outLine := strings.TrimSpace(stdout.String())
	if outLine != ref {
		t.Fatalf("stdout %q != returned ref %q", outLine, ref)
	}
	if strings.Contains(outLine, "\n") {
		t.Fatalf("stdout must be a single line, got %q", stdout.String())
	}
	if !strings.HasPrefix(outLine, "node-image.local/") {
		t.Fatalf("expected node-image.local/… tag, got %q", outLine)
	}
	if strings.Contains(outLine, "@sha256:") {
		t.Fatalf("--local must print a daemon tag, not a digest ref (Docker has no RepoDigests after load): %q", outLine)
	}

	cmd := exec.Command("docker", "run", "--rm", outLine)
	cmd.Env = os.Environ()
	var runOut, runErr bytes.Buffer
	cmd.Stdout = &runOut
	cmd.Stderr = &runErr
	if err := cmd.Run(); err != nil {
		t.Fatalf("docker run %s: %v\nstdout=%s\nstderr=%s\nbuild stderr=%s",
			outLine, err, runOut.String(), runErr.String(), stderr.String())
	}
	got := strings.TrimSpace(runOut.String())
	if got != "1m" {
		t.Fatalf("container output %q, want %q\nstderr=%s", got, "1m", runErr.String())
	}
}

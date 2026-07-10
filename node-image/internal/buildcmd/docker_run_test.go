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

const helloE2EExpectedOutput = "node-image-e2e-ok"

// requireDocker skips when the Docker CLI or daemon (local socket / DOCKER_HOST)
// is unavailable locally. On GitHub Actions it fails instead of skipping so CI
// cannot silently miss the e2e (ubuntu-latest runners have a Docker socket).
func requireDocker(t *testing.T) {
	t.Helper()
	inCI := os.Getenv("GITHUB_ACTIONS") == "true"
	if _, err := exec.LookPath("docker"); err != nil {
		if inCI {
			t.Fatalf("docker not on PATH in CI (required for e2e): %v", err)
		}
		t.Skip("docker not on PATH")
	}
	if err := exec.Command("docker", "info").Run(); err != nil {
		if inCI {
			t.Fatalf("docker daemon not available in CI (required for e2e): %v", err)
		}
		t.Skip("docker daemon not available (no local socket / DOCKER_HOST)")
	}
}

// TestE2EDockerSocketBuildAndRun builds testdata/hello-e2e with --local (load
// into the daemon via the Docker socket), then `docker run --rm` and asserts
// the container prints the expected marker. Skips when Docker is missing.
func TestE2EDockerSocketBuildAndRun(t *testing.T) {
	requireDocker(t)

	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "hello-e2e"))
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
		Repo:      "hello-e2e",
		Base:      config.DefaultBase,
		SkipBuild: true,
		Platforms: []string{plat},
		Tags:      []string{"e2e"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("node-image build --local: %v\nstderr=%s", err, stderr.String())
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
		t.Fatalf("--local must print a daemon tag, not a digest ref: %q", outLine)
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
	if got != helloE2EExpectedOutput {
		t.Fatalf("container output %q, want %q\nstderr=%s", got, helloE2EExpectedOutput, runErr.String())
	}
}

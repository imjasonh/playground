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

func dockerHostPlatform() string {
	if runtime.GOARCH == "arm64" {
		return "linux/arm64"
	}
	return "linux/amd64"
}

type dockerRunCase struct {
	name     string
	fixture  string // path under testdata/
	repo     string
	command  string // optional node-image --command
	runBuild bool   // if true, run host compile (needs pnpm); else --skip-build
	wantOut  string
	wantCode int // expected docker run exit code; 0 default
}

func buildLocalAndRun(t *testing.T, tc dockerRunCase) {
	t.Helper()

	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", filepath.FromSlash(tc.fixture)))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(fixture); err != nil {
		t.Fatalf("fixture %s: %v", fixture, err)
	}
	if tc.runBuild {
		if _, err := exec.LookPath("pnpm"); err != nil {
			if os.Getenv("GITHUB_ACTIONS") == "true" {
				t.Fatalf("pnpm required for %s compile e2e in CI: %v", tc.name, err)
			}
			t.Skip("pnpm not on PATH (needed to compile fixture)")
		}
	}

	repo := tc.repo
	if repo == "" {
		repo = strings.ReplaceAll(tc.name, "/", "-")
	}

	var stdout, stderr bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		Local:     true,
		Repo:      repo,
		Base:      config.DefaultBase,
		SkipBuild: !tc.runBuild,
		Platforms: []string{dockerHostPlatform()},
		Tags:      []string{"e2e"},
		Command:   tc.command,
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
	runErrCode := 0
	if err := cmd.Run(); err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			runErrCode = ee.ExitCode()
		} else {
			t.Fatalf("docker run %s: %v\nstdout=%s\nstderr=%s\nbuild stderr=%s",
				outLine, err, runOut.String(), runErr.String(), stderr.String())
		}
	}
	wantCode := tc.wantCode
	if runErrCode != wantCode {
		t.Fatalf("docker run exit %d, want %d\nstdout=%s\nstderr=%s\nbuild stderr=%s",
			runErrCode, wantCode, runOut.String(), runErr.String(), stderr.String())
	}
	got := strings.TrimSpace(runOut.String())
	if got != tc.wantOut {
		t.Fatalf("container output %q, want %q\nstderr=%s", got, tc.wantOut, runErr.String())
	}
}

// TestE2EDockerSocketBuildAndRun is the cheap smoke: pure JS + one dep.
func TestE2EDockerSocketBuildAndRun(t *testing.T) {
	requireDocker(t)
	buildLocalAndRun(t, dockerRunCase{
		name:    "hello-e2e",
		fixture: "hello-e2e",
		repo:    "hello-e2e",
		wantOut: helloE2EExpectedOutput,
	})
}

// TestE2EDockerSocketRuntimeCases covers shapes that often build cleanly but
// fail inside distroless at runtime (natives, patches, workspace links, bins,
// nested/scoped resolution, Cmd selection, app globs).
func TestE2EDockerSocketRuntimeCases(t *testing.T) {
	requireDocker(t)

	cases := []dockerRunCase{
		{
			name:    "optional-native-esbuild",
			fixture: "optional-platform",
			repo:    "optional-platform-e2e",
			wantOut: "esbuild-native-ok",
		},
		{
			name:    "workspace-link",
			fixture: "workspace-app/apps/api",
			repo:    "workspace-api-e2e",
			wantOut: "ok",
		},
		{
			name:    "patched-dep",
			fixture: "patched",
			repo:    "patched-e2e",
			wantOut: "patched-ok",
		},
		{
			name:    "nested-deps",
			fixture: "nested-deps",
			repo:    "nested-deps-e2e",
			wantOut: "ok",
		},
		{
			name:    "scoped-dep",
			fixture: "scoped-dep",
			repo:    "scoped-dep-e2e",
			wantOut: "ok",
		},
		{
			name:    "with-bin",
			fixture: "with-bin",
			repo:    "with-bin-e2e",
			wantOut: "ok",
		},
		{
			name:    "lifecycle-noop",
			fixture: "lifecycle-scripts",
			repo:    "lifecycle-e2e",
			wantOut: "ok",
		},
		{
			name:    "build-globs",
			fixture: "build-globs",
			repo:    "build-globs-e2e",
			wantOut: "globs-ok",
		},
		{
			name:    "multi-cmd-api",
			fixture: "multi-cmd",
			repo:    "multi-cmd-api-e2e",
			command: "api",
			wantOut: "api",
		},
		{
			name:    "multi-cmd-worker",
			fixture: "multi-cmd",
			repo:    "multi-cmd-worker-e2e",
			command: "worker",
			wantOut: "worker",
		},
		{
			name:    "catalog-app",
			fixture: "catalog-app",
			repo:    "catalog-e2e",
			wantOut: "1m",
		},
		{
			name:    "override-app",
			fixture: "override-app",
			repo:    "override-e2e",
			wantOut: "1m",
		},
		{
			name:     "ts-app-compile",
			fixture:  "ts-app",
			repo:     "ts-app-e2e",
			runBuild: true,
			wantOut:  "2m",
		},
	}

	for _, tc := range cases {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			buildLocalAndRun(t, tc)
		})
	}
}

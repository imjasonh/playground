package buildcmd_test

import (
	"bytes"
	"fmt"
	"io"
	"log"
	"net/http/httptest"
	"net/url"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/registry"
	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

var digestRefRE = regexp.MustCompile(`^[^@\s]+@sha256:[0-9a-f]{64}$`)

// TestBuildStdoutIsFullyResolvedRef asserts the ko-style contract:
// stdout is exactly one line — the fully resolved image ref — so
// `docker run --rm $(node-image build …)` can consume it.
func TestBuildStdoutIsFullyResolvedRef(t *testing.T) {
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}

	s := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(s.Close)
	u, err := url.Parse(s.URL)
	if err != nil {
		t.Fatal(err)
	}
	repo := fmt.Sprintf("%s/node-image-stdout-test", u.Host)

	var stdout, stderr bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		Repo:      repo,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Tags:      []string{"test"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, stderr.String())
	}

	out := stdout.String()
	if strings.Contains(out, "\n\n") {
		t.Fatalf("stdout has blank lines: %q", out)
	}
	lines := strings.Split(strings.TrimSuffix(out, "\n"), "\n")
	if len(lines) != 1 {
		t.Fatalf("stdout must be exactly one line, got %d: %q\nstderr=%s", len(lines), out, stderr.String())
	}
	got := lines[0]
	if got != ref {
		t.Fatalf("returned ref %q != stdout %q", ref, got)
	}
	if !digestRefRE.MatchString(got) {
		t.Fatalf("stdout is not a fully resolved digest ref: %q", got)
	}
	if !strings.HasPrefix(got, repo+"@sha256:") {
		t.Fatalf("stdout ref %q does not start with repo %q", got, repo)
	}
	// Progress / diagnostics must not leak onto stdout.
	if strings.Contains(out, "wrote ") || strings.Contains(out, "compiling") || strings.Contains(out, "layer budget") {
		t.Fatalf("progress leaked onto stdout: %q", out)
	}
}

package apppack_test

import (
	"io"
	"log"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/registry"

	"github.com/imjasonh/playground/sshcloud/internal/apppack"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
)

func TestBuildPushFortuneMaterialize(t *testing.T) {
	if _, err := exec.LookPath("mkfs.ext4"); err != nil {
		t.Skip("mkfs.ext4 not available")
	}
	bin := filepath.Join(t.TempDir(), "fortune")
	cmd := exec.Command("go", "build", "-o", bin, "github.com/imjasonh/playground/sshcloud/cmd/fortune")
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH=amd64")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("build fortune: %v\n%s", err, out)
	}

	img, err := apppack.Build(apppack.Spec{
		Binary:    bin,
		GuestPath: "/fortune",
		Cmd:       []string{"-listen", "0.0.0.0:22", "-ca", "/ca.pub"},
	})
	if err != nil {
		t.Fatal(err)
	}

	srv := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(srv.Close)
	host := strings.TrimPrefix(srv.URL, "http://")
	ref, err := apppack.Push(img, host+"/sshcloud/fortune:test")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(ref, "@sha256:") {
		t.Fatalf("ref %q", ref)
	}

	res, err := ocirootfs.Materialize(t.Context(), ref, ocirootfs.Options{
		CacheDir: t.TempDir(),
		SizeMB:   32,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := res.Spec.Validate(); err != nil {
		t.Fatal(err)
	}
	argv := strings.Join(guestinit.Argv(res.Spec), " ")
	if argv != "/fortune -listen 0.0.0.0:22 -ca /ca.pub" {
		t.Fatalf("spec argv %q", argv)
	}
}

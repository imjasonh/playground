package gateway_test

import (
	"bytes"
	"context"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

func TestProxyFortuneWithCert(t *testing.T) {
	ca, err := userca.LoadOrGenerate("")
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	caPub := filepath.Join(dir, "ca.pub")
	if err := os.WriteFile(caPub, ca.PublicAuthorizedKey(), 0o644); err != nil {
		t.Fatal(err)
	}
	bin := filepath.Join(dir, "fortune")
	cmd := exec.Command("go", "build", "-o", bin, "github.com/imjasonh/playground/sshcloud/cmd/fortune")
	cmd.Env = append(os.Environ(), "GOTOOLCHAIN=auto")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("build fortune: %v\n%s", err, out)
	}

	lf := backend.NewLocalFortune(bin, caPub)
	defer lf.Stop()
	addr, err := lf.Ensure()
	if err != nil {
		t.Fatal(err)
	}

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: eofReader{}, Writer: &out}

	if err := gateway.ProxySSH(context.Background(), rw, ca, "alice", addr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), "hello alice") {
		t.Fatalf("output: %q", out.String())
	}
}

type eofReader struct{}

func (eofReader) Read([]byte) (int, error) { return 0, io.EOF }

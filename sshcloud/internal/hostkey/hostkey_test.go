package hostkey

import (
	"os"
	"path/filepath"
	"testing"
)

func TestLoadOrGeneratePersists(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	path := filepath.Join(dir, "ssh_host_ed25519_key")
	s1, err := LoadOrGenerate(path)
	if err != nil {
		t.Fatal(err)
	}
	s2, err := LoadOrGenerate(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(s1.PublicKey().Marshal()) != string(s2.PublicKey().Marshal()) {
		t.Fatal("expected same host key after reload")
	}
	fi, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	if fi.Mode().Perm()&0o077 != 0 {
		t.Fatalf("host key permissions too open: %v", fi.Mode())
	}
}

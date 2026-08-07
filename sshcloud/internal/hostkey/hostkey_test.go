package hostkey

import (
	"os"
	"path/filepath"
	"sync"
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

func TestLoadOrGenerateRejectsPermissiveExistingKey(t *testing.T) {
	t.Parallel()
	data, _, err := Generate()
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "ssh_host_ed25519_key")
	if err := os.WriteFile(path, data, 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(path, 0o640); err != nil {
		t.Fatal(err)
	}
	if _, err := LoadOrGenerate(path); err == nil {
		t.Fatal("group-readable private key was accepted")
	}
}

func TestConcurrentLoadOrGenerateUsesSingleExclusiveCreate(t *testing.T) {
	t.Parallel()
	path := filepath.Join(t.TempDir(), "ssh_host_ed25519_key")
	const callers = 16
	start := make(chan struct{})
	results := make(chan string, callers)
	errs := make(chan error, callers)
	var wg sync.WaitGroup
	for range callers {
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			signer, err := LoadOrGenerate(path)
			if err != nil {
				errs <- err
				return
			}
			results <- string(signer.PublicKey().Marshal())
		}()
	}
	close(start)
	wg.Wait()
	close(results)
	close(errs)
	for err := range errs {
		t.Fatal(err)
	}
	var want string
	for got := range results {
		if want == "" {
			want = got
		} else if got != want {
			t.Fatal("concurrent callers observed different generated keys")
		}
	}
	if want == "" {
		t.Fatal("no caller returned a host key")
	}
}

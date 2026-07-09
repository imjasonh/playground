package fetch_test

import (
	"crypto/sha512"
	"encoding/base64"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/node-image/internal/fetch"
)

func TestEnsureUsesTimeoutClient(t *testing.T) {
	c := &fetch.Cache{Dir: t.TempDir()}
	// Hang forever — default client timeout should abort.
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		time.Sleep(5 * time.Second)
	}))
	t.Cleanup(srv.Close)
	c.HTTPClient = &http.Client{Timeout: 50 * time.Millisecond}
	body := []byte("hello-tarball")
	sum := sha512.Sum512(body)
	integrity := "sha512-" + base64.StdEncoding.EncodeToString(sum[:])
	_, err := c.Ensure(srv.URL+"/pkg.tgz", integrity)
	if err == nil {
		t.Fatal("expected timeout error")
	}
}

func TestEnsureConcurrentUniqueTemp(t *testing.T) {
	body := []byte("concurrent-tarball-body")
	sum := sha512.Sum512(body)
	integrity := "sha512-" + base64.StdEncoding.EncodeToString(sum[:])
	var hits int
	var mu sync.Mutex
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		hits++
		mu.Unlock()
		time.Sleep(20 * time.Millisecond)
		_, _ = w.Write(body)
	}))
	t.Cleanup(srv.Close)

	dir := t.TempDir()
	c := &fetch.Cache{Dir: dir, HTTPClient: srv.Client()}
	var wg sync.WaitGroup
	errs := make(chan error, 8)
	for i := 0; i < 8; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			path, err := c.Ensure(srv.URL+"/pkg.tgz", integrity)
			if err != nil {
				errs <- err
				return
			}
			b, err := os.ReadFile(path)
			if err != nil {
				errs <- err
				return
			}
			if string(b) != string(body) {
				errs <- fmt.Errorf("bad body %q", b)
			}
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Fatal(err)
	}
	entries, _ := os.ReadDir(dir)
	for _, e := range entries {
		if filepath.Ext(e.Name()) == ".tmp" || (len(e.Name()) > 4 && e.Name()[len(e.Name())-4:] == ".tmp") {
			t.Fatalf("leftover temp file: %s", e.Name())
		}
	}
	_ = hits
}

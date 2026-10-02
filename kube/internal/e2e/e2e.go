// Package e2e helps end-to-end tests run controllers against a real API
// server. Tests skip unless $KUBEBUILDER_ASSETS names a directory with etcd
// and kube-apiserver binaries.
package e2e

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"os"
	"reflect"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/envtest"
)

var (
	env     *envtest.Env
	envErr  error
	envOnce sync.Once
)

// Main runs a test binary's tests and stops the shared control plane, if
// one was started, afterward.
func Main(m *testing.M) {
	code := m.Run()
	if env != nil {
		env.Stop()
	}
	os.Exit(code)
}

// Env returns the shared control plane, starting it on first use, or skips
// the test when $KUBEBUILDER_ASSETS is unset.
func Env(t testing.TB) *envtest.Env {
	t.Helper()
	assets := os.Getenv("KUBEBUILDER_ASSETS")
	if assets == "" {
		t.Skip("set KUBEBUILDER_ASSETS to a directory with etcd and kube-apiserver to run end-to-end tests")
	}
	envOnce.Do(func() {
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		env, envErr = envtest.Start(ctx, assets)
	})
	if envErr != nil {
		t.Fatalf("starting control plane: %v", envErr)
	}
	return env
}

// Client returns an administrator's client for the shared control plane.
func Client(t testing.TB) *client.Client {
	t.Helper()
	cfg, err := client.LoadKubeconfig([]string{Env(t).Kubeconfig}, "")
	if err != nil {
		t.Fatal(err)
	}
	c, err := client.New(cfg, "e2e")
	if err != nil {
		t.Fatal(err)
	}
	return c
}

// Namespace creates a namespace with a unique name for one test.
func Namespace(t testing.TB, c *client.Client) string {
	t.Helper()
	b := make([]byte, 3)
	_, _ = rand.Read(b)
	name := strings.ToLower(strings.NewReplacer("/", "-", "_", "-").Replace(t.Name()))
	if len(name) > 50 {
		name = name[:50]
	}
	name = strings.Trim(name, "-") + "-" + hex.EncodeToString(b)
	ns := map[string]any{"apiVersion": "v1", "kind": "Namespace", "metadata": map[string]any{"name": name}}
	if err := c.Create(t.Context(), "/api/v1/namespaces", ns, nil); err != nil {
		t.Fatal(err)
	}
	return name
}

// Run runs controllers in m until the test ends.
func Run(t testing.TB, m *kube.Manager, controllers ...kube.Controller) {
	t.Helper()
	if m.Kubeconfig == "" {
		m.Kubeconfig = Env(t).Kubeconfig
	}
	if m.Logger == nil {
		m.Logger = Logger(t)
	}
	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan error, 1)
	go func() { done <- m.Run(ctx, controllers...) }()
	t.Cleanup(func() {
		cancel()
		select {
		case err := <-done:
			if err != nil {
				t.Errorf("manager: %v", err)
			}
		case <-time.After(30 * time.Second):
			t.Error("manager didn't stop within 30s")
		}
	})
}

// Logger returns a logger that writes to the test log. Set KUBE_E2E_DEBUG to
// include debug messages.
func Logger(t testing.TB) *slog.Logger {
	level := slog.LevelInfo
	if os.Getenv("KUBE_E2E_DEBUG") != "" {
		level = slog.LevelDebug
	}
	return slog.New(slog.NewTextHandler(testWriter{t}, &slog.HandlerOptions{Level: level}))
}

type testWriter struct{ t testing.TB }

func (w testWriter) Write(p []byte) (int, error) {
	w.t.Helper()
	w.t.Log(strings.TrimSuffix(string(p), "\n"))
	return len(p), nil
}

var _ io.Writer = testWriter{}

// Eventually calls f until it returns nil, failing the test if it still
// returns an error after timeout.
func Eventually(t testing.TB, timeout time.Duration, f func() error) {
	t.Helper()
	deadline := time.Now().Add(timeout)
	for {
		err := f()
		if err == nil {
			return
		}
		if time.Now().After(deadline) {
			t.Fatalf("condition not met after %v: %v", timeout, err)
		}
		time.Sleep(100 * time.Millisecond)
	}
}

// Never fails the test if f returns an error at any point during d.
func Never(t testing.TB, d time.Duration, f func() error) {
	t.Helper()
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		if err := f(); err != nil {
			t.Fatal(err)
		}
		time.Sleep(100 * time.Millisecond)
	}
}

// Get decodes the object at path into out, returning an error that says so
// when it doesn't exist. It zeroes out first: encoding/json reuses slice
// elements and keeps fields that the new JSON omits, which would show stale
// values when a test polls into the same variable.
func Get(ctx context.Context, c *client.Client, path string, out any) error {
	reflect.ValueOf(out).Elem().SetZero()
	err := c.Get(ctx, path, out)
	if client.IsNotFound(err) {
		return fmt.Errorf("%s not found", path)
	}
	return err
}

// Gone returns nil when the object at path doesn't exist.
func Gone(ctx context.Context, c *client.Client, path string) error {
	var out map[string]any
	err := c.Get(ctx, path, &out)
	switch {
	case client.IsNotFound(err):
		return nil
	case err != nil:
		return err
	default:
		return errors.New(path + " still exists")
	}
}

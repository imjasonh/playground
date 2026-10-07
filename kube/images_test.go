package kube

import (
	"bytes"
	"context"
	"errors"
	"flag"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
	"github.com/imjasonh/playground/kube/internal/registry"
)

const testDigest = "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

// commandLine replaces flag.CommandLine until the test ends.
func commandLine(t *testing.T) *flag.FlagSet {
	t.Helper()
	saved := flag.CommandLine
	flag.CommandLine = flag.NewFlagSet("test", flag.ContinueOnError)
	t.Cleanup(func() { flag.CommandLine = saved })
	return flag.CommandLine
}

// lockedBuffer is a bytes.Buffer that goroutines can write to at once.
type lockedBuffer struct {
	mu  sync.Mutex
	buf bytes.Buffer
}

func (b *lockedBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.buf.Write(p)
}

func (b *lockedBuffer) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.buf.String()
}

func TestImageFlag(t *testing.T) {
	fs := commandLine(t)
	fs.SetOutput(new(bytes.Buffer))
	img := Image("image", "nginx:1.27", "image that serves the site")
	var other string
	ImageVar(fs, &other, "other-image", "", "image of the sidecar")
	if *img != "nginx:1.27" || other != "" {
		t.Fatalf("defaults: -image=%q, -other-image=%q", *img, other)
	}
	if err := fs.Parse([]string{"-image=ghcr.io/you/site@" + testDigest, "-other-image", "localhost:5000/proxy:v2"}); err != nil {
		t.Fatal(err)
	}
	if *img != "ghcr.io/you/site@"+testDigest || other != "localhost:5000/proxy:v2" {
		t.Errorf("after Parse: -image=%q, -other-image=%q", *img, other)
	}
	if err := fs.Parse([]string{"-other-image="}); err != nil || other != "" {
		t.Errorf("-other-image= set %q, %v; want empty", other, err)
	}
	if err := fs.Parse([]string{"-image=Nginx"}); err == nil || !strings.Contains(err.Error(), `invalid value "Nginx" for flag -image: not an image reference`) {
		t.Errorf("-image=Nginx: %v, want an error", err)
	}

	var help bytes.Buffer
	fs.SetOutput(&help)
	fs.PrintDefaults()
	want := "  -image value\n    \timage that serves the site (default nginx:1.27)\n  -other-image value\n    \timage of the sidecar\n"
	if help.String() != want {
		t.Errorf("PrintDefaults() =\n%s\nwant\n%s", help.String(), want)
	}
}

// podSpecWith returns a Pod spec with an init container, regular
// containers, and an ephemeral container with the given images, and a
// container without an image.
func podSpecWith(init, app, pinned, taggedAndPinned, debug string) map[string]any {
	return map[string]any{
		"initContainers": []any{map[string]any{"name": "init", "image": init}},
		"containers": []any{
			map[string]any{"name": "app", "image": app},
			map[string]any{"name": "pinned", "image": pinned},
			map[string]any{"name": "tagged-and-pinned", "image": taggedAndPinned},
			map[string]any{"name": "no-image"},
		},
		"ephemeralContainers": []any{map[string]any{"name": "debug", "image": debug}},
	}
}

// containerImages returns the image of each container in spec, by name.
func containerImages(spec map[string]any) map[string]string {
	out := map[string]string{}
	for _, list := range []string{"initContainers", "containers", "ephemeralContainers"} {
		for _, c := range spec[list].([]any) {
			c := c.(map[string]any)
			if image, ok := c["image"].(string); ok {
				out[c["name"].(string)] = image
			}
		}
	}
	return out
}

func TestPinImages(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	app := imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	init := imagetest.Base(t, reg+"/init:v1", "linux/arm64")
	debug := imagetest.Base(t, reg+"/debug:latest", "linux/s390x")
	// A reference with a digest needs no registry, so these name a
	// registry that doesn't exist.
	pinned := "registry.invalid/app@" + testDigest
	taggedAndPinned := "registry.invalid/app:v2@" + testDigest

	d := &imageDigests{digest: registry.Digest}
	var resolved []string
	for _, tt := range []struct {
		apiVersion, kind string
		path             []string
	}{
		{"v1", "Pod", []string{"spec"}},
		{"v1", "PodTemplate", []string{"template", "spec"}},
		{"v1", "ReplicationController", []string{"spec", "template", "spec"}},
		{"apps/v1", "Deployment", []string{"spec", "template", "spec"}},
		{"apps/v1", "StatefulSet", []string{"spec", "template", "spec"}},
		{"apps/v1", "DaemonSet", []string{"spec", "template", "spec"}},
		{"apps/v1", "ReplicaSet", []string{"spec", "template", "spec"}},
		{"batch/v1", "Job", []string{"spec", "template", "spec"}},
		{"batch/v1", "CronJob", []string{"spec", "jobTemplate", "spec", "template", "spec"}},
	} {
		spec := podSpecWith(reg+"/init:v1", reg+"/app:v1", pinned, taggedAndPinned, reg+"/debug")
		obj := map[string]any{"apiVersion": tt.apiVersion, "kind": tt.kind, "metadata": map[string]any{"name": "web"}}
		parent := obj
		for _, key := range tt.path[:len(tt.path)-1] {
			child := map[string]any{}
			parent[key], parent = child, child
		}
		parent[tt.path[len(tt.path)-1]] = spec
		if err := d.pinImages(t.Context(), jsonMap(obj), func(from, to string) { resolved = append(resolved, from+" "+to) }); err != nil {
			t.Errorf("%s: %v", tt.kind, err)
			continue
		}
		want := map[string]string{
			"init":              reg + "/init@" + init,
			"app":               reg + "/app@" + app,
			"pinned":            pinned,
			"tagged-and-pinned": taggedAndPinned,
			"debug":             reg + "/debug@" + debug,
		}
		if got := containerImages(spec); !reflect.DeepEqual(got, want) {
			t.Errorf("%s: images = %v, want %v", tt.kind, got, want)
		}
	}
	want := []string{
		reg + "/init:v1 " + reg + "/init@" + init,
		reg + "/app:v1 " + reg + "/app@" + app,
		reg + "/debug " + reg + "/debug@" + debug,
	}
	if !reflect.DeepEqual(resolved, want) {
		t.Errorf("resolved %q, want each tag once: %q", resolved, want)
	}
}

func TestPinImagesLeavesOtherObjects(t *testing.T) {
	d := &imageDigests{digest: func(_ context.Context, ref string) (string, error) {
		t.Errorf("resolved %s", ref)
		return testDigest, nil
	}}
	containers := []any{map[string]any{"name": "app", "image": "nginx:1.27"}}
	for _, obj := range []map[string]any{
		{"apiVersion": "v1", "kind": "ConfigMap", "data": map[string]any{"image": "nginx:1.27"}},
		{"apiVersion": "example.com/v1", "kind": "Deployment", "spec": map[string]any{"template": map[string]any{"spec": map[string]any{"containers": containers}}}},
		{"apiVersion": "example.com/v1", "kind": "Pod", "spec": map[string]any{"containers": containers}},
		{"apiVersion": "apps/v1", "kind": "Deployment", "metadata": map[string]any{"name": "web", "labels": map[string]any{"image": "nginx:1.27"}}},
		{"apiVersion": "apps/v1", "kind": "Deployment", "spec": map[string]any{"replicas": 2, "template": nil}},
		{"apiVersion": "v1", "kind": "Pod", "spec": map[string]any{"containers": "nginx:1.27"}},
	} {
		if err := d.pinImages(t.Context(), jsonMap(obj), func(string, string) {}); err != nil {
			t.Errorf("pinImages(%v): %v", obj, err)
		}
	}
	if got := containers[0].(map[string]any)["image"]; got != "nginx:1.27" {
		t.Errorf("image = %v, want it unchanged", got)
	}
}

func TestPinImagesFails(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	d := &imageDigests{digest: registry.Digest}
	for image, want := range map[string]string{
		reg + "/app:nope": "container web: resolving image " + reg + "/app:nope: GET http://" + reg + "/v2/app/manifests/nope: 404 Not Found: MANIFEST_UNKNOWN",
		"Nginx:1.27":      `container web: image "Nginx:1.27": not an image reference`,
	} {
		pod := map[string]any{"apiVersion": "v1", "kind": "Pod", "spec": map[string]any{"containers": []any{map[string]any{"name": "web", "image": image}}}}
		if err := d.pinImages(t.Context(), jsonMap(pod), func(string, string) {}); err == nil || !strings.HasPrefix(err.Error(), want) {
			t.Errorf("pinImages(%s) = %v, want an error that starts %q", image, err, want)
		}
	}
}

func TestImageDigestsResolveEachTagOnce(t *testing.T) {
	var calls atomic.Int32
	release := make(chan struct{})
	d := &imageDigests{digest: func(context.Context, string) (string, error) {
		calls.Add(1)
		<-release
		return testDigest, nil
	}}
	// Each spelling names the same tag on Docker Hub.
	spellings := []string{"nginx", "nginx:latest", "docker.io/library/nginx:latest", "index.docker.io/library/nginx"}
	got := make([]string, 4*len(spellings))
	var wg sync.WaitGroup
	for i := range got {
		wg.Go(func() {
			p, _, err := d.pin(t.Context(), spellings[i%len(spellings)])
			if err != nil {
				t.Error(err)
			}
			got[i] = p
		})
	}
	close(release)
	wg.Wait()
	if n := calls.Load(); n != 1 {
		t.Errorf("asked the registry %d times, want once", n)
	}
	for i, p := range got {
		if want := strings.TrimSuffix(spellings[i%len(spellings)], ":latest") + "@" + testDigest; p != want {
			t.Errorf("pin(%q) = %q, want %q", spellings[i%len(spellings)], p, want)
		}
	}
	if p, resolved, err := d.pin(t.Context(), "ghcr.io/you/app@"+testDigest); p != "ghcr.io/you/app@"+testDigest || resolved || err != nil || calls.Load() != 1 {
		t.Errorf("pin of a digest = %q, %v, %v; want it unchanged without asking the registry", p, resolved, err)
	}
}

func TestImageDigestsRetryFailures(t *testing.T) {
	var calls int
	d := &imageDigests{digest: func(context.Context, string) (string, error) {
		if calls++; calls == 1 {
			return "", errors.New("unavailable")
		}
		return testDigest, nil
	}}
	if _, _, err := d.pin(t.Context(), "ghcr.io/you/app:v1"); err == nil || err.Error() != "resolving image ghcr.io/you/app:v1: unavailable" {
		t.Fatalf("first pin: %v, want the registry's error", err)
	}
	for i, wantResolved := range []bool{true, false} {
		p, resolved, err := d.pin(t.Context(), "ghcr.io/you/app:v1")
		if p != "ghcr.io/you/app@"+testDigest || resolved != wantResolved || err != nil {
			t.Errorf("pin %d after the failure = %q, %v, %v; want the digest, %v", i+2, p, resolved, err, wantResolved)
		}
	}
	if calls != 2 {
		t.Errorf("asked the registry %d times, want 2", calls)
	}
}

func TestImageDigestsWaitForContext(t *testing.T) {
	started, release := make(chan struct{}), make(chan struct{})
	d := &imageDigests{digest: func(context.Context, string) (string, error) {
		close(started)
		<-release
		return testDigest, nil
	}}
	done := make(chan error, 1)
	go func() {
		_, _, err := d.pin(t.Context(), "ghcr.io/you/app:v1")
		done <- err
	}()
	<-started
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	if _, _, err := d.pin(ctx, "ghcr.io/you/app:v1"); !errors.Is(err, context.Canceled) {
		t.Errorf("pin with a canceled context = %v, want context.Canceled", err)
	}
	close(release)
	if err := <-done; err != nil {
		t.Error(err)
	}
}

// probe is a controller that records an image flag's value when the
// manager prepares it, and then stops the manager.
type probe struct {
	stub
	image    *string
	prepared bool
	saw      string
}

var errProbe = errors.New("the probe stops the manager")

func (p *probe) prepare(context.Context, *Manager) error {
	p.prepared, p.saw = true, *p.image
	return errProbe
}

// noAPI returns a client for an API server that fails the test on every
// request.
func noAPI(t *testing.T) *client.Client {
	t.Helper()
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		t.Errorf("request to the API server: %s %s", r.Method, r.URL)
		w.WriteHeader(http.StatusInternalServerError)
	}))
	t.Cleanup(srv.Close)
	c, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	return c
}

func TestRunResolvesImageFlags(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	digest := imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	commandLine(t)
	app := Image("app-image", reg+"/app:v1", "image that runs the app")
	pinned := Image("pinned-image", "registry.invalid/app@"+testDigest, "image by digest")
	empty := Image("empty-image", "", "optional image")

	var logs lockedBuffer
	p := &probe{image: app}
	m := &Manager{client: noAPI(t), Logger: slog.New(slog.NewTextHandler(&logs, nil))}
	if err := m.Run(t.Context(), p); !errors.Is(err, errProbe) {
		t.Fatalf("Run() = %v, want the probe's error", err)
	}
	want := reg + "/app@" + digest
	if p.saw != want || *app != want {
		t.Errorf("the controller saw -app-image=%q, and it's now %q; want %q", p.saw, *app, want)
	}
	if *pinned != "registry.invalid/app@"+testDigest || *empty != "" {
		t.Errorf("-pinned-image=%q, -empty-image=%q; want them unchanged", *pinned, *empty)
	}
	if line := `msg="resolved image flag" flag=app-image image=` + reg + `/app:v1 pinned=` + want; !strings.Contains(logs.String(), line) {
		t.Errorf("the log doesn't have %s:\n%s", line, logs.String())
	}
}

func TestRunFailsOnImageFlagThatDoesNotResolve(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	commandLine(t)
	app := Image("app-image", reg+"/app:nope", "image that runs the app")

	p := &probe{image: app}
	m := &Manager{client: noAPI(t), Logger: slog.New(slog.DiscardHandler)}
	err := m.Run(t.Context(), p)
	if want := "-app-image: resolving image " + reg + "/app:nope: "; err == nil || !strings.HasPrefix(err.Error(), want) {
		t.Errorf("Run() = %v, want an error that starts %q", err, want)
	}
	if p.prepared {
		t.Error("a controller started before Run resolved the image flags")
	}
}

func TestInstallResolvesImagesBeforeApplying(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	objs, err := parseManifest([]byte(`apiVersion: v1
kind: ConfigMap
metadata:
  name: settings
  namespace: shop
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web
  namespace: shop
spec:
  template:
    spec:
      containers:
      - name: web
        image: ` + reg + `/app:nope
`))
	if err != nil {
		t.Fatal(err)
	}
	m := &Manager{client: noAPI(t), log: slog.New(slog.DiscardHandler)}
	err = (&installer{objects: objs}).setup(t.Context(), m)
	if want := "installing Deployment web: container web: resolving image " + reg + "/app:nope: "; err == nil || !strings.HasPrefix(err.Error(), want) {
		t.Errorf("setup() = %v, want an error that starts %q, before it applies the ConfigMap", err, want)
	}
}

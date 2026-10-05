package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"io"
	"maps"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/gocache"
	"github.com/imjasonh/playground/kube"
)

const testImage = "registry.example.com/check-gotest@sha256:0123456789abcdef"

// withGoCache sets -go-cache for one test.
func withGoCache(t *testing.T) {
	t.Helper()
	saved := goCache
	t.Cleanup(func() { goCache = saved })
	t.Setenv("KUBE_IMAGE", testImage)
	if err := setGoCache("http://go-cache.go-cache/"); err != nil {
		t.Fatal(err)
	}
}

func env(c Container, name string) string {
	for _, e := range c.Env {
		if e.Name == name {
			return e.Value
		}
	}
	return ""
}

func mount(c Container, volume string) *VolumeMount {
	for i := range c.VolumeMounts {
		if c.VolumeMounts[i].Name == volume {
			return &c.VolumeMounts[i]
		}
	}
	return nil
}

func TestSetGoCache(t *testing.T) {
	saved := goCache
	t.Cleanup(func() { goCache = saved })
	for _, bad := range []string{"go-cache.go-cache", "ftp://go-cache", "http://", "http://go-cache?x=1", "http://go-cache#x", "http://[::1"} {
		if err := setGoCache(bad); err == nil {
			t.Errorf("setGoCache(%q) succeeded", bad)
		}
	}
	t.Log("generate parses -go-cache where KUBE_IMAGE isn't set, because only the Deployment sets it.")
	t.Setenv("KUBE_IMAGE", "")
	if err := setGoCache("https://go-cache.example.com/"); err != nil || goCache.url != "https://go-cache.example.com" {
		t.Errorf("setGoCache: %v, goCache = %+v", err, goCache)
	}
}

func TestGoCacheNeedsImage(t *testing.T) {
	withGoCache(t)
	t.Setenv("KUBE_IMAGE", "")
	b, repo := branch()
	ctx, rec := kube.Fake(t.Context(), b, repo)
	if err := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}).Reconcile(ctx, b); err == nil || !strings.Contains(err.Error(), "KUBE_IMAGE") {
		t.Errorf("Reconcile = %v, want an error about KUBE_IMAGE", err)
	}
	if res := b.Status.Checks.Result; res == nil || res.State != gitk8s.Error || !strings.Contains(res.Message, "KUBE_IMAGE") {
		t.Errorf("result = %+v, want Error about KUBE_IMAGE", res)
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 0 {
		t.Errorf("owned Pods = %+v, want none without the image for cacheprog and upload", pods)
	}
}

func TestNoGoCache(t *testing.T) {
	b, repo := branch()
	spec := kube.Owned[Pod](reconcileWith(t, b, repo))[0].Spec
	test := spec.Containers[0]
	if len(spec.InitContainers) != 1 || len(spec.Volumes) != 2 || env(test, "GOCACHEPROG") != "" || env(test, "GOPROXY") != "off" {
		t.Errorf("without -go-cache, the Pod changed: %+v", spec)
	}
}

func TestGoCachePod(t *testing.T) {
	withGoCache(t)
	b, repo := branch()
	pods := kube.Owned[Pod](reconcileWith(t, b, repo))
	if len(pods) != 1 {
		t.Fatalf("owned Pods = %+v", pods)
	}
	spec := pods[0].Spec
	var names []string
	for _, c := range spec.InitContainers {
		names = append(names, c.Name)
	}
	if want := []string{"fetch", "cacheprog", "build", "upload"}; !slices.Equal(names, want) {
		t.Fatalf("init containers = %v, want %v", names, want)
	}
	fetch, install, build, upload := spec.InitContainers[0], spec.InitContainers[1], spec.InitContainers[2], spec.InitContainers[3]
	test := spec.Containers[0]
	all := append(slices.Clone(spec.InitContainers), test)

	t.Log("The tokens read or write only the repository's build cache, and only build and upload mount one.")
	audiences := map[string]string{}
	for _, v := range spec.Volumes {
		if v.Projected != nil {
			sat := v.Projected.Sources[0].ServiceAccountToken
			audiences[v.Name] = sat.Audience
			if *sat.ExpirationSeconds != 600 || sat.Path != "token" {
				t.Errorf("volume %s: %+v", v.Name, sat)
			}
		}
	}
	want := map[string]string{
		"go-cache-read":  gocache.ReadAudience("default", "app"),
		"go-cache-write": gocache.WriteAudience("default", "app"),
	}
	if !maps.Equal(audiences, want) {
		t.Errorf("token audiences = %v, want %v", audiences, want)
	}
	for _, c := range all {
		read, write := mount(c, "go-cache-read"), mount(c, "go-cache-write")
		if (read != nil) != (c.Name == "build") || (write != nil) != (c.Name == "upload") {
			t.Errorf("container %s mounts the read token: %t, the write token: %t", c.Name, read != nil, write != nil)
		}
		if (read != nil && !read.ReadOnly) || (write != nil && !write.ReadOnly) {
			t.Errorf("container %s can write its token volume", c.Name)
		}
	}
	if mount(fetch, "go-cache") != nil {
		t.Error("fetch mounts the go-cache volume")
	}
	if m := mount(upload, "go-cache"); m == nil || !m.ReadOnly || mount(upload, "src") != nil {
		t.Errorf("upload should read the outputs and nothing from the branch: %+v", upload.VolumeMounts)
	}

	t.Log("Only build reads the build cache on go-cache; the test container's GOCACHEPROG stays local.")
	remote := "http://go-cache.go-cache/cache/default/app"
	if want := []string{"/go-cache/check-gotest", "cacheprog", "-build", "-dir=/go-cache/outputs", "-remote=" + remote, "-token-file=/var/run/secrets/go-cache/token"}; !slices.Equal(build.Command, want) {
		t.Errorf("build runs %q, want %q", build.Command, want)
	}
	if got, want := env(test, "GOCACHEPROG"), "/go-cache/check-gotest cacheprog -dir=/go-cache/outputs"; got != want {
		t.Errorf("the test container's GOCACHEPROG = %q, want %q", got, want)
	}
	if want := []string{"cacheprog", "-upload", "-dir=/go-cache/outputs", "-remote=" + remote, "-token-file=/var/run/secrets/go-cache/token"}; !slices.Equal(upload.Args, want) {
		t.Errorf("upload's args = %q, want %q", upload.Args, want)
	}
	if want := []string{"cacheprog", "-install=/go-cache/check-gotest"}; install.Image != testImage || upload.Image != testImage || !slices.Equal(install.Args, want) {
		t.Errorf("cacheprog and upload should run %s: %+v, %+v", testImage, install, upload)
	}

	t.Log("build compiles in the test container's environment, so their action IDs match.")
	if build.Image != test.Image || build.WorkingDir != test.WorkingDir || !slices.Equal(build.Env, test.Env) {
		t.Errorf("build = %+v, test = %+v", build, test)
	}
	if got := env(test, "GOPROXY"); got != "http://go-cache.go-cache/mod" {
		t.Errorf("GOPROXY = %q, want go-cache's module proxy", got)
	}

	for _, c := range all {
		sc := c.SecurityContext
		if *sc.AllowPrivilegeEscalation || !*sc.ReadOnlyRootFilesystem || !slices.Equal(sc.Capabilities.Drop, []string{"ALL"}) {
			t.Errorf("container %s isn't locked down: %+v", c.Name, sc)
		}
		if secret := slices.ContainsFunc(c.Env, func(e EnvVar) bool { return e.ValueFrom != nil }); secret != (c.Name == "fetch") {
			t.Errorf("container %s sees the repository's credentials: %t", c.Name, secret)
		}
	}
	if *spec.AutomountServiceAccountToken {
		t.Error("the Pod mounts its service account token")
	}
}

func TestReportsGoCacheFailure(t *testing.T) {
	withGoCache(t)
	b, repo := branch()
	p := pod("Failed", &Terminated{}, nil)
	s := ContainerStatus{Name: "build"}
	s.State.Terminated = &Terminated{ExitCode: 1, Message: "go: errors parsing go.mod:\ngo.mod:3: unknown directive: bogus"}
	p.Status.InitContainerStatuses = append(p.Status.InitContainerStatuses, s)
	reconcileWith(t, b, repo, p)
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "build: go: errors parsing go.mod") {
		t.Errorf("result = %+v, want Failed with build's error", res)
	}
}

func TestCacheprogInstall(t *testing.T) {
	path := filepath.Join(t.TempDir(), "check-gotest")
	if code := cacheprog([]string{"-install=" + path}, nil, io.Discard, io.Discard); code != 0 {
		t.Fatalf("cacheprog -install = %d", code)
	}
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	want, err := os.ReadFile(exe)
	if err != nil {
		t.Fatal(err)
	}
	got, err := os.ReadFile(path)
	if err != nil || !bytes.Equal(got, want) {
		t.Errorf("installed %d bytes (%v), want a copy of the %d-byte binary", len(got), err, len(want))
	}
	if fi, err := os.Stat(path); err != nil || fi.Mode().Perm()&0o111 == 0 {
		t.Errorf("the copy isn't executable: %v", err)
	}
	if code := cacheprog([]string{"-install=" + path}, nil, io.Discard, io.Discard); code == 0 {
		t.Error("installing over an existing file succeeded")
	}
}

// putRequests is what the go command sends to store body as an action's
// output, and then to close the program.
func putRequests(action []byte, body []byte) string {
	sum := sha256.Sum256(body)
	req, _ := json.Marshal(map[string]any{"ID": 1, "Command": "put", "ActionID": action, "OutputID": sum[:], "BodySize": len(body)})
	enc, _ := json.Marshal(body)
	return string(req) + "\n" + string(enc) + "\n" + `{"ID":2,"Command":"close"}` + "\n"
}

func TestCacheprogUploads(t *testing.T) {
	dir := t.TempDir()
	action := bytes.Repeat([]byte{1}, sha256.Size)
	var out bytes.Buffer
	if code := cacheprog([]string{"-dir=" + dir, "-share"}, strings.NewReader(putRequests(action, []byte("compiled"))), &out, io.Discard); code != 0 {
		t.Fatalf("cacheprog -share = %d; output:\n%s", code, out.String())
	}
	t.Log("upload leaves out what the go command built without -share, as in the test container.")
	local := bytes.Repeat([]byte{2}, sha256.Size)
	if code := cacheprog([]string{"-dir=" + dir}, strings.NewReader(putRequests(local, []byte("from the branch"))), &out, io.Discard); code != 0 {
		t.Fatalf("cacheprog = %d; output:\n%s", code, out.String())
	}
	tokenFile := filepath.Join(t.TempDir(), "token")
	if err := os.WriteFile(tokenFile, []byte("write-token\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	var (
		mu     sync.Mutex
		status = http.StatusCreated
		puts   []string
	)
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		body, _ := io.ReadAll(r.Body)
		mu.Lock()
		defer mu.Unlock()
		puts = append(puts, r.Method+" "+r.URL.Path+" "+r.Header.Get("Authorization")+" "+string(body))
		w.WriteHeader(status)
	}))
	defer srv.Close()
	upload := func() string {
		t.Helper()
		out.Reset()
		args := []string{"-upload", "-dir=" + dir, "-remote=" + srv.URL + "/cache/default/app", "-token-file=" + tokenFile}
		if code := cacheprog(args, nil, &out, io.Discard); code != 0 {
			t.Fatalf("cacheprog -upload = %d", code)
		}
		return out.String()
	}
	if got := upload(); !strings.Contains(got, "go-cache stored 1 build outputs, and already had 0") {
		t.Errorf("upload printed %q", got)
	}
	mu.Lock()
	want := "PUT /cache/default/app/" + hex.EncodeToString(action) + " Bearer write-token compiled"
	if len(puts) != 1 || puts[0] != want {
		t.Errorf("requests = %q, want %q", puts, want)
	}
	status = http.StatusInternalServerError
	mu.Unlock()

	t.Log("A failed upload doesn't stop the tests.")
	if got := upload(); !strings.Contains(got, "1 of 1 uploads failed") {
		t.Errorf("upload printed %q", got)
	}
}

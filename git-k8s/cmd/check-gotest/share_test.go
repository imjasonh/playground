package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/gocache"
	"github.com/imjasonh/playground/kube"
)

// TestMain runs the test binary as check-gotest's image does, for the test
// Pods that TestSharedOutputs runs.
func TestMain(m *testing.M) {
	if len(os.Args) > 1 && os.Args[1] == "cacheprog" {
		os.Exit(cacheprog(os.Args[2:], os.Stdin, os.Stdout, os.Stderr))
	}
	os.Exit(m.Run())
}

// valBranch is a module whose package fast returns VAL from inc/val.h, a
// header outside fast's directory that fast's assembly includes. fast's
// test passes only when VAL is 41.
func valBranch(val int) map[string]string {
	return map[string]string{
		"go.mod":            "module example.com/m\n\ngo 1.24\n",
		"inc/val.h":         fmt.Sprintf("#define VAL $%d\n", val),
		"fast/fast.go":      "package fast\n\n// Val is implemented in assembly.\nfunc Val() int64\n",
		"fast/fast_amd64.s": "#include \"textflag.h\"\n#include \"../inc/val.h\"\n\nTEXT ·Val(SB),NOSPLIT,$0-8\n\tMOVQ\tVAL, AX\n\tMOVQ\tAX, ret+0(FP)\n\tRET\n",
		"fast/fast_arm64.s": "#include \"textflag.h\"\n#include \"../inc/val.h\"\n\nTEXT ·Val(SB),NOSPLIT,$0-8\n\tMOVD\tVAL, R0\n\tMOVD\tR0, ret+0(FP)\n\tRET\n",
		"fast/fast_test.go": "package fast\n\nimport \"testing\"\n\nfunc TestVal(t *testing.T) {\n\tif got := Val(); got != 41 {\n\t\tt.Fatalf(\"Val() = %d, want 41\", got)\n\t}\n}\n",
	}
}

// fakeGoCache is go-cache's build cache for the repository default/app. A
// projected token's content is its audience, so a token is its audience.
type fakeGoCache struct {
	mu      sync.Mutex
	outputs map[string][]byte
	hits    int
}

// reads returns how many outputs f has served.
func (f *fakeGoCache) reads() int {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.hits
}

func (f *fakeGoCache) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	action, ok := strings.CutPrefix(r.URL.Path, gocache.Path("default", "app")+"/")
	token := strings.TrimPrefix(r.Header.Get("Authorization"), "Bearer ")
	f.mu.Lock()
	defer f.mu.Unlock()
	switch {
	case !ok:
		http.NotFound(w, r)
	case r.Method == http.MethodGet && token == gocache.ReadAudience("default", "app"):
		body, ok := f.outputs[action]
		if !ok {
			http.NotFound(w, r)
			return
		}
		f.hits++
		sum := sha256.Sum256(body)
		w.Header().Set(gocache.OutputIDHeader, hex.EncodeToString(sum[:]))
		w.Header().Set("Content-Length", strconv.Itoa(len(body)))
		w.Write(body)
	case r.Method == http.MethodPut && token == gocache.WriteAudience("default", "app"):
		body, err := io.ReadAll(r.Body)
		sum := sha256.Sum256(body)
		if err != nil || r.Header.Get(gocache.OutputIDHeader) != hex.EncodeToString(sum[:]) {
			http.Error(w, "bad output", http.StatusBadRequest)
			return
		}
		if _, ok := f.outputs[action]; ok {
			w.WriteHeader(http.StatusOK)
			return
		}
		f.outputs[action] = body
		w.WriteHeader(http.StatusCreated)
	default:
		http.Error(w, "denied", http.StatusForbidden)
	}
}

// goCachePod returns the spec of the test Pod that the check declares with
// -go-cache set to url.
func goCachePod(t *testing.T, url string) PodSpec {
	t.Helper()
	saved := goCache
	t.Cleanup(func() { goCache = saved })
	t.Setenv("KUBE_IMAGE", testImage)
	if err := setGoCache(url); err != nil {
		t.Fatal(err)
	}
	b, repo := branch()
	return kube.Owned[Pod](reconcileWith(t, b, repo))[0].Spec
}

// runPod runs a test Pod's containers on this machine, in order, with the
// files of branch as the fetched head. Each volume is an empty directory
// in root, which a container sees at its mount paths, and check-gotest's
// image is the test binary. Pods that run in one root see their volumes at
// the same paths, as Pods in a cluster do. runPod returns the test
// container's output, and whether the tests passed.
func runPod(t *testing.T, root string, spec PodSpec, branch map[string]string) (string, bool) {
	t.Helper()
	self, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	volumes := map[string]string{}
	for _, v := range spec.Volumes {
		volumes[v.Name] = filepath.Join(root, v.Name)
		if err := os.RemoveAll(volumes[v.Name]); err != nil {
			t.Fatal(err)
		}
		if err := os.Mkdir(volumes[v.Name], 0o755); err != nil {
			t.Fatal(err)
		}
		if v.Projected != nil {
			sat := v.Projected.Sources[0].ServiceAccountToken
			if err := os.WriteFile(filepath.Join(volumes[v.Name], sat.Path), []byte(sat.Audience), 0o600); err != nil {
				t.Fatal(err)
			}
		}
	}
	for name, src := range branch {
		path := filepath.Join(volumes["src"], "repo", name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	run := func(c Container) (string, error) {
		mounts := slices.Clone(c.VolumeMounts)
		slices.SortFunc(mounts, func(a, b VolumeMount) int { return len(b.MountPath) - len(a.MountPath) })
		local := func(path string) string {
			for _, m := range mounts {
				if rest, ok := strings.CutPrefix(path, m.MountPath); ok && (rest == "" || rest[0] == '/') {
					return volumes[m.Name] + rest
				}
			}
			return path
		}
		// translate replaces the paths in a command-line argument or an
		// environment variable, alone or as a flag's value.
		translate := func(s string) string {
			words := strings.Split(s, " ")
			for i, w := range words {
				if name, value, ok := strings.Cut(w, "="); ok && strings.HasPrefix(value, "/") {
					words[i] = name + "=" + local(value)
				} else if strings.HasPrefix(w, "/") {
					words[i] = local(w)
				}
			}
			return strings.Join(words, " ")
		}
		argv := slices.Concat(c.Command, c.Args)
		if len(c.Command) == 0 {
			argv = append([]string{self}, c.Args...)
		}
		for i := range argv {
			argv[i] = translate(argv[i])
		}
		cmd := exec.Command(argv[0], argv[1:]...)
		cmd.Env = []string{"PATH=" + os.Getenv("PATH")}
		for _, e := range c.Env {
			cmd.Env = append(cmd.Env, e.Name+"="+translate(e.Value))
		}
		cmd.Dir = t.TempDir()
		if c.WorkingDir != "" {
			cmd.Dir = local(c.WorkingDir)
		}
		out, err := cmd.CombinedOutput()
		return string(out), err
	}
	for _, c := range spec.InitContainers {
		if c.Name == "fetch" {
			continue
		}
		out, err := run(c)
		if err != nil {
			t.Fatalf("init container %s: %v\n%s", c.Name, err, out)
		}
		t.Logf("init container %s:\n%s", c.Name, out)
	}
	out, err := run(spec.Containers[0])
	return out, err == nil
}

// TestSharedOutputs runs two branches' test Pods, one after the other, with
// one build cache. The branches differ only in inc/val.h, which package
// fast's assembly includes from outside fast's directory. The go command
// leaves that header out of fast's action ID, so both branches compute one
// action ID for fast, and compile different outputs for it. Each Pod's
// tests must pass or fail as they would with an empty build cache, so a
// branch can't make main's tests fail, and main can't make a branch's tests
// pass, whichever ran first.
func TestSharedOutputs(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("go isn't installed")
	}
	if runtime.GOARCH != "amd64" && runtime.GOARCH != "arm64" {
		t.Skipf("package fast has no assembly for %s", runtime.GOARCH)
	}
	good, bad := valBranch(41), valBranch(666)
	for _, tc := range []struct {
		name          string
		first, second map[string]string
		secondPasses  bool
	}{
		{"main after a branch that changed the header", bad, good, true},
		{"a branch that changed the header after main", good, bad, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			cache := &fakeGoCache{outputs: map[string][]byte{}}
			srv := httptest.NewServer(cache)
			t.Cleanup(srv.Close)
			spec, root := goCachePod(t, srv.URL), t.TempDir()
			if out, passed := runPod(t, root, spec, tc.first); passed == tc.secondPasses {
				t.Fatalf("the first Pod's tests passed: %t, want %t:\n%s", passed, !tc.secondPasses, out)
			}
			read := cache.reads()
			if out, passed := runPod(t, root, spec, tc.second); passed != tc.secondPasses {
				t.Errorf("the second Pod's tests passed: %t, want %t, as with an empty build cache:\n%s", passed, tc.secondPasses, out)
			}
			if cache.reads() == read {
				t.Error("the second Pod read no outputs from go-cache")
			}
		})
	}
}

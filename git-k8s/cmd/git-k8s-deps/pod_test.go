package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"maps"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	"golang.org/x/mod/modfile"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/goproxytest"
	"github.com/imjasonh/playground/kube"
)

var updateGolden = flag.Bool("update", false, "rewrite testdata/pod.json")

func TestPod(t *testing.T) {
	u := &updater{
		goImage: "go", gitImage: "git", resultImage: "agent-runner", timeout: time.Minute, sourceSize: "2Gi", goCacheSize: "4Gi",
		goSumDB: "sum.golang.org", runtimeClass: "gvisor",
		proxy: newProxy([]string{"https://proxy.example.com"}, time.Hour, time.Now),
	}
	b := &Branch{Object: kube.Meta("app-main", nil)}
	b.Spec.Branch = "main"
	repo := &gitk8s.Repository{Spec: gitk8s.GitRepositorySpec{URL: "https://git.example.com/app.git", SecretRef: &gitk8s.SecretRef{Name: "app-creds"}}}
	ups := []update{{module: greet, version: "v1.1.0", from: map[string]string{"tools": "v1.0.0", ".": "v1.0.0"}}}
	p := u.pod(b, repo, "0123abcd", 0, ups)
	var got strings.Builder
	enc := json.NewEncoder(&got)
	enc.SetEscapeHTML(false)
	enc.SetIndent("", "  ")
	if err := enc.Encode(p); err != nil {
		t.Fatal(err)
	}
	golden := filepath.Join("testdata", "pod.json")
	if *updateGolden {
		if err := os.WriteFile(golden, []byte(got.String()), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	want, err := os.ReadFile(golden)
	if err != nil {
		t.Fatal(err)
	}
	if g, w := strings.Split(got.String(), "\n"), strings.Split(string(want), "\n"); !slices.Equal(g, w) {
		i := 0
		for i < len(g)-1 && i < len(w)-1 && g[i] == w[i] {
			i++
		}
		t.Errorf("the Pod differs from %s at line %d, which go test -run TestPod -update rewrites:\ngot:  %s\nwant: %s", golden, i+1, g[i], w[i])
	}

	if got, want := env(p.Spec.InitContainers[1], "UPDATES"), "example.com/greet v1.1.0 . tools\n"; got != want {
		t.Errorf("UPDATES = %q, want %q", got, want)
	}
	for _, c := range p.Spec.InitContainers {
		if got := env(c, "GIT_ALLOW_PROTOCOL"); got != allowProtocol {
			t.Errorf("the %s container's GIT_ALLOW_PROTOCOL = %q, want %q", c.Name, got, allowProtocol)
		}
	}
	if again := u.pod(b, repo, "0123abcd", 0, ups); again.Name != p.Name {
		t.Errorf("the same Pod has names %s and %s", p.Name, again.Name)
	}
	other := []update{{module: greet, version: "v1.2.0", from: ups[0].from}}
	for _, q := range []string{u.pod(b, repo, "0123abcd", 1, ups).Name, u.pod(b, repo, "4567cdef", 0, ups).Name, u.pod(b, repo, "0123abcd", 0, other).Name} {
		if q == p.Name {
			t.Errorf("a Pod with another attempt, head, or update has the name %s", q)
		}
	}

	sizes := map[string]string{}
	for _, v := range p.Spec.Volumes {
		sizes[v.Name] = v.EmptyDir.SizeLimit
	}
	if want := map[string]string{"src": "2Gi", "tmp": "4Gi", "result": "64Mi"}; !maps.Equal(sizes, want) {
		t.Errorf("volume sizes = %v, want %v", sizes, want)
	}
	for _, c := range slices.Concat(p.Spec.InitContainers, p.Spec.Containers) {
		want := "6464Mi"
		if c.Name == "result" {
			want = "256Mi"
		}
		if r := c.Resources; r.Requests["ephemeral-storage"] == "" || string(r.Limits["ephemeral-storage"]) != want {
			t.Errorf("the %s container requests %q of ephemeral storage and limits it to %q, want a limit of %s", c.Name, r.Requests["ephemeral-storage"], r.Limits["ephemeral-storage"], want)
		}
	}
	u.sourceSize, u.goCacheSize = "10Gi", "6Gi"
	p = u.pod(b, repo, "0123abcd", 0, ups)
	if src, tmp := p.Spec.Volumes[0].EmptyDir.SizeLimit, p.Spec.Volumes[1].EmptyDir.SizeLimit; src != "10Gi" || tmp != "6Gi" {
		t.Errorf("with -source-size=10Gi and -go-cache-size=6Gi, the src and tmp volumes hold %s and %s", src, tmp)
	}
	if got := p.Spec.InitContainers[0].Resources.Limits["ephemeral-storage"]; got != "16704Mi" {
		t.Errorf("ephemeral-storage limit = %s, want 16704Mi, which holds every volume and the logs", got)
	}
}

func TestSizes(t *testing.T) {
	for s, want := range map[string]int64{
		"2Gi": 2 << 30, "500M": 500e6, "1": 1, "1k": 1000, "64Ki": 64 << 10, "3Ti": 3 << 40, "2097151Ti": 2097151 << 40,
		"": 0, "0": 0, "-1Gi": 0, "+1Gi": 0, "1.5Gi": 0, "2GB": 0, "2gi": 0, "Gi": 0, "1e9": 0, "2Pi": 0, "2097152Ti": 0,
	} {
		if got := parseSize(s); got != want {
			t.Errorf("parseSize(%q) = %d, want %d", s, got, want)
		}
	}
	for n, want := range map[int64]string{1000: "1000", 2048: "2Ki", 1536 << 20: "1536Mi", 1 << 30: "1Gi", 5 << 40: "5Ti", 1 << 50: "1024Ti"} {
		if got := formatSize(n); got != want {
			t.Errorf("formatSize(%d) = %q, want %q", n, got, want)
		}
	}
}

// TestScripts runs the update Pod's scripts with git and the go command,
// against a git server and a module proxy over HTTP.
func TestScripts(t *testing.T) {
	for _, bin := range []string{"sh", "git", "go", "base64", "sha256sum", "tail", "cut"} {
		if _, err := exec.LookPath(bin); err != nil {
			t.Skipf("%s isn't installed", bin)
		}
	}
	root := t.TempDir()
	publish := func(mod, version, code string) {
		t.Helper()
		dir := t.TempDir()
		write(t, dir, "go.mod", "module "+mod+"\n\ngo 1.24\n")
		write(t, dir, "x.go", code)
		if err := goproxytest.Publish(root, dir, version, longAgo); err != nil {
			t.Fatal(err)
		}
	}
	publish(greet, "v1.0.0", "package greet\n\nfunc Hello() string { return \"hello\" }\n")
	publish(greet, "v1.1.0", "package greet\n\nfunc Hello() string { return \"hello!\" }\n")
	publish("example.com/other", "v1.0.0", "package other\n")
	publish("example.com/other", "v1.0.1", "package other\n\nconst X = 1\n")
	proxy := httptest.NewServer(http.FileServer(http.Dir(root)))
	t.Cleanup(proxy.Close)

	home := t.TempDir()
	base := []string{"HOME=" + home, "PATH=" + os.Getenv("PATH"), "GIT_CONFIG_NOSYSTEM=1", "GIT_TERMINAL_PROMPT=0", "GIT_ALLOW_PROTOCOL=" + allowProtocol}
	goEnv := append(base,
		"GOPATH="+filepath.Join(home, "go"), "GOCACHE="+filepath.Join(home, "go-build"),
		"GOTOOLCHAIN=local", "GOWORK=off", "GOPROXY="+proxy.URL, "GOSUMDB=off", "CGO_ENABLED=0",
		// The test's cleanup can't delete a read-only module cache.
		"GOFLAGS=-modcacherw",
	)
	run := func(dir, script string, env []string) (string, error) {
		t.Helper()
		cmd := exec.Command("sh", "-c", script)
		cmd.Dir, cmd.Env = dir, env
		out, err := cmd.CombinedOutput()
		return string(out), err
	}

	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	w.Write("go.mod", "module example.com/app\n\ngo 1.24\n\nrequire (\n\texample.com/greet v1.0.0\n\texample.com/other v1.0.0\n)\n")
	w.Write("app.go", "package app\n\nimport (\n\t\"example.com/greet\"\n\t_ \"example.com/other\"\n)\n\nvar Greeting = greet.Hello()\n")
	w.Write("tools/go.mod", "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n\n"+
		"replace (\n\texample.com/z => ./z\n\texample.com/b => ./b\n)\n\nexclude (\n\texample.com/greet v0.9.0\n\texample.com/greet v0.8.0\n)\n")
	w.Write("tools/tools.go", "package tools\n\nimport _ \"example.com/greet\"\n")
	if out, err := run(w.Dir, "go mod tidy", goEnv); err != nil {
		t.Fatalf("go mod tidy: %v\n%s", err, out)
	}
	head := w.Commit("main")
	w.Push("main")
	mods := map[string]*modFile{}
	for _, dir := range []string{".", "tools"} {
		data, err := os.ReadFile(filepath.Join(w.Dir, dir, "go.mod"))
		if err != nil {
			t.Fatal(err)
		}
		f, err := modfile.Parse(dir+"/go.mod", data, nil)
		if err != nil {
			t.Fatal(err)
		}
		mods[dir] = &modFile{data: data, file: f}
	}

	src := t.TempDir()
	repo := filepath.Join(src, "repo")
	prepare := append(base, "URL="+srv.Remote("app").URL, "BRANCH=main", "REPO="+repo, "GIT_USERNAME="+srv.Username, "GIT_PASSWORD="+srv.Password)
	t.Log("The prepare script stops if the branch moved.")
	moved := append(prepare[:len(prepare):len(prepare)], "HEAD=4567cdef4567cdef4567cdef4567cdef4567cdef", "REPO="+filepath.Join(src, "moved"))
	if out, err := run(src, prepareScript, moved); err == nil || !strings.Contains(out, "main no longer points to 4567cdef") {
		t.Fatalf("prepare with another head = %v\n%s", err, out)
	}
	t.Log("A URL that looks like an option is still a URL.")
	marker := filepath.Join(t.TempDir(), "ran")
	option := append(prepare[:len(prepare):len(prepare)], "URL=--upload-pack=echo >"+marker, "HEAD="+head, "REPO="+filepath.Join(src, "option"))
	if out, err := run(src, prepareScript, option); err == nil {
		t.Errorf("prepare succeeded with an option for a URL\n%s", out)
	}
	if _, err := os.Stat(marker); !os.IsNotExist(err) {
		t.Errorf("prepare ran the URL's --upload-pack: %v", err)
	}
	t.Log("A URL can't name a remote helper.")
	bin, ran := t.TempDir(), filepath.Join(t.TempDir(), "ran")
	if err := os.WriteFile(filepath.Join(bin, "git-remote-evil"), []byte("#!/bin/sh\ntouch "+ran+"\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	helper := append(prepare[:len(prepare):len(prepare)], "URL=evil::x", "HEAD="+head, "REPO="+filepath.Join(src, "helper"), "PATH="+bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	if out, err := run(src, prepareScript, helper); err == nil || !strings.Contains(out, "not allowed") {
		t.Errorf("prepare with a remote helper's URL = %v, want git to refuse the transport\n%s", err, out)
	}
	if _, err := os.Stat(ran); !os.IsNotExist(err) {
		t.Errorf("prepare ran the remote helper: %v", err)
	}
	t.Log("A URL can't name a repository on the Pod's file system.")
	for _, url := range []string{w.Dir, "file://" + filepath.ToSlash(w.Dir)} {
		local := append(prepare[:len(prepare):len(prepare)], "URL="+url, "HEAD="+head, "REPO="+filepath.Join(src, "local"))
		if out, err := run(src, prepareScript, local); err == nil || !strings.Contains(out, "transport 'file' not allowed") {
			t.Errorf("prepare with the URL %s = %v, want git to refuse the file transport\n%s", url, err, out)
		}
	}
	if out, err := run(src, prepareScript, append(prepare, "HEAD="+head)); err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	if out, err := run(repo, "git rev-parse HEAD && git config --get credential.helper || true", base); err != nil || strings.TrimSpace(out) != head {
		t.Fatalf("after prepare, HEAD and the credential helper = %q, %v; want only %s", out, err, head)
	}

	t.Log("The update script makes each update from the parent's files.")
	results, logs := filepath.Join(t.TempDir(), "result.json"), filepath.Join(t.TempDir(), "update.log")
	termination := filepath.Join(t.TempDir(), "termination-log")
	ups := []update{
		{module: greet, version: "v1.1.0", from: map[string]string{".": "v1.0.0", "tools": "v1.0.0"}},
		{module: "example.com/missing", version: "v1.0.0", from: map[string]string{".": "v0.1.0"}},
		{module: "example.com/other", version: "v1.0.1", from: map[string]string{".": "v1.0.0"}},
	}
	update := append(goEnv, "UPDATES="+updateLines(ups), "REPO="+repo, "RESULT_FILE="+results, "LOG_FILE="+logs, "TERMINATION_LOG="+termination)
	if out, err := run(src, updateScript, update); err != nil {
		t.Fatalf("update: %v\n%s", err, out)
	}
	body, err := os.ReadFile(results)
	if err != nil {
		t.Fatal(err)
	}
	digest, err := os.ReadFile(termination)
	if err != nil {
		t.Fatal(err)
	}
	if sum := sha256.Sum256(body); string(digest) != "sha256:"+hex.EncodeToString(sum[:]) {
		t.Errorf("the termination log = %q, want the result's digest", digest)
	}
	out, err := parseResult(body, ups)
	if err != nil {
		t.Fatalf("parseResult() = %v\n%s", err, body)
	}

	g := out[ups[0].key()]
	if g.err != "" || len(g.files) != 4 {
		t.Fatalf("greet's outcome = %q with files %v, want go.mod and go.sum in . and tools", g.err, len(g.files))
	}
	if err := checkResult(mods, ups[0], g.files); err != nil {
		t.Errorf("checkResult() = %v", err)
	}
	if !strings.Contains(string(g.files["tools/go.mod"]), "\texample.com/b => ./b\n\texample.com/z => ./z\n") {
		t.Errorf("go get didn't sort tools/go.mod's replace block:\n%s", g.files["tools/go.mod"])
	}
	for path, want := range map[string][]string{
		"go.sum":       {"example.com/greet v1.1.0 h1:", "example.com/greet v1.1.0/go.mod h1:", "example.com/other v1.0.0 h1:"},
		"tools/go.sum": {"example.com/greet v1.1.0 h1:", "example.com/greet v1.1.0/go.mod h1:"},
	} {
		for _, line := range want {
			if !strings.Contains(string(g.files[path]), line) {
				t.Errorf("%s doesn't have %q:\n%s", path, line, g.files[path])
			}
		}
	}
	if strings.Contains(string(g.files["go.sum"]), "greet v1.0.0 h1:") {
		t.Errorf("go mod tidy didn't run in the root module, which was tidy:\n%s", g.files["go.sum"])
	}

	if m := out[ups[1].key()]; !strings.Contains(m.err, "example.com/missing") || m.files != nil {
		t.Errorf("the missing module's outcome = %q, want go's error", m.err)
	}

	o := out[ups[2].key()]
	if err := checkResult(mods, ups[2], o.files); o.err != "" || err != nil {
		t.Fatalf("other's outcome = %q, checkResult() = %v", o.err, err)
	}
	if f, err := modfile.Parse("go.mod", o.files["go.mod"], nil); err != nil || !requires(f, greet, "v1.0.0") || o.files["tools/go.mod"] != nil {
		t.Errorf("other's update didn't start from the parent's files:\n%s", o.files["go.mod"])
	}
}

// TestPrepareScriptGitArguments runs the prepare script with a git that
// records its arguments instead of running, so a URL that looks like an
// option has to show up after --end-of-options.
func TestPrepareScriptGitArguments(t *testing.T) {
	if _, err := exec.LookPath("sh"); err != nil {
		t.Skip("sh isn't installed")
	}
	dir, bin := t.TempDir(), t.TempDir()
	args, repo := filepath.Join(dir, "args"), filepath.Join(dir, "repo")
	stub := "#!/bin/sh\nfor a; do printf '[%s]' \"$a\"; done >>\"$ARGS\"\necho >>\"$ARGS\"\n" +
		"case $1 in\ninit) mkdir -p \"$REPO/.git/info\" ;;\nrev-parse) echo \"$HEAD\" ;;\nesac\n"
	if err := os.WriteFile(filepath.Join(bin, "git"), []byte(stub), 0o755); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("sh", "-c", prepareScript)
	cmd.Dir = dir
	cmd.Env = []string{
		"PATH=" + bin + string(os.PathListSeparator) + os.Getenv("PATH"), "ARGS=" + args,
		"URL=--upload-pack=touch ran", "BRANCH=main", "HEAD=0123abcd", "REPO=" + repo,
	}
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	data, err := os.ReadFile(args)
	if err != nil {
		t.Fatal(err)
	}
	want := []string{
		"[init][-q][--end-of-options][" + repo + "]",
		"[fetch][-q][--depth=1][--end-of-options][--upload-pack=touch ran][refs/heads/main]",
		"[rev-parse][--verify][--end-of-options][FETCH_HEAD]",
		"[config][--unset][credential.helper]",
		"[switch][-q][--detach][--end-of-options][FETCH_HEAD]",
	}
	if got := strings.Split(strings.TrimSuffix(string(data), "\n"), "\n"); !slices.Equal(got, want) {
		t.Errorf("the prepare script ran git with:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func write(t *testing.T, dir, name, content string) {
	t.Helper()
	if err := os.WriteFile(filepath.Join(dir, name), []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

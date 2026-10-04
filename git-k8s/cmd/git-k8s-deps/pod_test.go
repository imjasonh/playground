package main

import (
	"crypto/sha256"
	"encoding/hex"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"golang.org/x/mod/modfile"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/goproxytest"
	"github.com/imjasonh/playground/kube"
)

func TestPod(t *testing.T) {
	u := &updater{goImage: "go", gitImage: "git", resultImage: "agent-runner", timeout: time.Minute, proxy: newProxy([]string{"https://proxy.example.com"}, time.Hour, time.Now)}
	b := &Branch{Object: kube.Meta("app-main", nil)}
	b.Spec.Branch = "main"
	repo := &gitk8s.Repository{Spec: gitk8s.GitRepositorySpec{URL: "https://git.example.com/app.git"}}
	ups := []update{{module: greet, version: "v1.1.0", from: map[string]string{"tools": "v1.0.0", ".": "v1.0.0"}}}
	p := u.pod(b, repo, "0123abcd", 0, ups)
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
	w.Write("tools/go.mod", "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n")
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

func write(t *testing.T, dir, name, content string) {
	t.Helper()
	if err := os.WriteFile(filepath.Join(dir, name), []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

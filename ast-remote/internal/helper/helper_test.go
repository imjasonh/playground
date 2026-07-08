package helper_test

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/helper"
)

func TestRemoteHelperPushFetch(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not available")
	}

	tmp := t.TempDir()
	srcRepo := filepath.Join(tmp, "src")
	storeDir := filepath.Join(tmp, "ast-store")
	cloneDir := filepath.Join(tmp, "clone")

	mustRun(t, tmp, "git", "init", "-b", "main", srcRepo)
	mustRun(t, srcRepo, "git", "config", "user.email", "test@example.com")
	mustRun(t, srcRepo, "git", "config", "user.name", "Test")

	write(t, filepath.Join(srcRepo, "hello.go"), `package main

import "fmt"

func main() {
	fmt.Println("hi")
}
`)
	write(t, filepath.Join(srcRepo, "util.py"), "def add(a, b):\n    return a + b\n")
	write(t, filepath.Join(srcRepo, "notes.txt"), "plain text stays raw\n")
	mustRun(t, srcRepo, "git", "add", ".")
	mustRun(t, srcRepo, "git", "commit", "-m", "init")

	gitDir := filepath.Join(srcRepo, ".git")
	oid := strings.TrimSpace(mustOutput(t, srcRepo, "git", "rev-parse", "HEAD"))

	var out bytes.Buffer
	var errBuf bytes.Buffer
	in := strings.NewReader(strings.Join([]string{
		"capabilities",
		"list for-push",
		"push refs/heads/main:refs/heads/main",
		"",
	}, "\n") + "\n")

	t.Setenv("GIT_DIR", gitDir)
	t.Setenv("GIT_WORK_TREE", srcRepo)
	err := helper.Run("origin", "ast::"+storeDir, in, &out, &errBuf)
	if err != nil {
		t.Fatalf("push helper: %v\nstderr=%s\nstdout=%s", err, errBuf.String(), out.String())
	}
	if !strings.Contains(out.String(), "ok refs/heads/main") {
		t.Fatalf("expected ok push, got %q\nstderr=%s", out.String(), errBuf.String())
	}

	mustRun(t, tmp, "git", "init", "-b", "main", cloneDir)
	mustRun(t, cloneDir, "git", "config", "user.email", "test@example.com")
	mustRun(t, cloneDir, "git", "config", "user.name", "Test")
	cloneGit := filepath.Join(cloneDir, ".git")

	var out2 bytes.Buffer
	var err2 bytes.Buffer
	in2 := strings.NewReader(strings.Join([]string{
		"capabilities",
		"list",
		"fetch " + oid + " refs/heads/main",
		"",
	}, "\n") + "\n")
	t.Setenv("GIT_DIR", cloneGit)
	t.Setenv("GIT_WORK_TREE", cloneDir)
	err = helper.Run("origin", "ast::"+storeDir, in2, &out2, &err2)
	if err != nil {
		t.Fatalf("fetch helper: %v\nstderr=%s\nstdout=%s", err, err2.String(), out2.String())
	}

	mustRun(t, cloneDir, "git", "update-ref", "refs/heads/main", oid)
	mustRun(t, cloneDir, "git", "checkout", "-f", "main")

	gotGo, err := os.ReadFile(filepath.Join(cloneDir, "hello.go"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(gotGo), `fmt.Println("hi")`) {
		t.Fatalf("cloned go file wrong: %s", gotGo)
	}
	gotPy, err := os.ReadFile(filepath.Join(cloneDir, "util.py"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(gotPy), "def add") {
		t.Fatalf("cloned py file wrong: %s", gotPy)
	}
}

func testEnv() []string {
	env := os.Environ()
	out := make([]string, 0, len(env)+2)
	for _, e := range env {
		if strings.HasPrefix(e, "GIT_DIR=") || strings.HasPrefix(e, "GIT_WORK_TREE=") {
			continue
		}
		out = append(out, e)
	}
	out = append(out,
		"GIT_AUTHOR_DATE=2020-01-01T00:00:00",
		"GIT_COMMITTER_DATE=2020-01-01T00:00:00",
	)
	return out
}

func mustRun(t *testing.T, dir string, name string, args ...string) {
	t.Helper()
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	cmd.Env = testEnv()
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("%s %v: %v\n%s", name, args, err, out)
	}
}

func mustOutput(t *testing.T, dir string, name string, args ...string) string {
	t.Helper()
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	cmd.Env = testEnv()
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("%s %v: %v\n%s", name, args, err, out)
	}
	return string(out)
}

func write(t *testing.T, path, body string) {
	t.Helper()
	if err := os.WriteFile(path, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
}

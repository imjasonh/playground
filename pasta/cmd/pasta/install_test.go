package main

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// isolateGit skips the test when git is missing and gives git an empty
// config file, so a global core.hooksPath or commit signing on the
// machine can't leak into the test.
func isolateGit(t *testing.T) {
	t.Helper()
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not installed")
	}
	t.Setenv("GIT_CONFIG_GLOBAL", filepath.Join(t.TempDir(), "gitconfig"))
	t.Setenv("GIT_CONFIG_NOSYSTEM", "1")
	t.Setenv("GIT_AUTHOR_NAME", "Pasta Test")
	t.Setenv("GIT_AUTHOR_EMAIL", "pasta@example.com")
	t.Setenv("GIT_COMMITTER_NAME", "Pasta Test")
	t.Setenv("GIT_COMMITTER_EMAIL", "pasta@example.com")
}

// newHookRepo creates a git repository with a .pasta/ directory and
// makes it the current directory. It points the hook at a stub pasta
// that writes its physical working directory and arguments to log and
// exits with $STUB_PASTA_EXIT.
func newHookRepo(t *testing.T) (repo, log string) {
	t.Helper()
	isolateGit(t)
	t.Setenv("STUB_PASTA_EXIT", "0")

	repo = t.TempDir()
	runGit(t, repo, "init", "--quiet")
	mkdirAll(t, filepath.Join(repo, DefaultRulesDir))

	stubDir := t.TempDir()
	log = filepath.Join(stubDir, "log")
	stub := filepath.Join(stubDir, "pasta")
	writeStubPasta(t, stub, log)
	orig := executable
	executable = func() (string, error) { return stub, nil }
	t.Cleanup(func() { executable = orig })

	t.Chdir(repo)
	return repo, log
}

func writeStubPasta(t *testing.T, path, log string) {
	t.Helper()
	writeFile(t, path, `#!/bin/sh
{ pwd -P; printf '%s\n' "$@"; } >`+shellQuote(log)+`
exit "${STUB_PASTA_EXIT:-0}"
`, 0o755)
}

func runGit(t *testing.T, dir string, args ...string) string {
	t.Helper()
	cmd := exec.Command("git", args...)
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("git %s: %v\n%s", strings.Join(args, " "), err, out)
	}
	return string(out)
}

func mkdirAll(t *testing.T, dir string) {
	t.Helper()
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
}

func writeFile(t *testing.T, path, content string, perm os.FileMode) {
	t.Helper()
	mkdirAll(t, filepath.Dir(path))
	if err := os.WriteFile(path, []byte(content), perm); err != nil {
		t.Fatal(err)
	}
}

func readFile(t *testing.T, path string) string {
	t.Helper()
	b, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}

func assertNotExist(t *testing.T, path string) {
	t.Helper()
	if _, err := os.Lstat(path); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("%s: want no file, got %v", path, err)
	}
}

// stubLog is what the stub pasta logs when it runs in dir with args.
func stubLog(t *testing.T, dir string, args ...string) string {
	t.Helper()
	resolved, err := filepath.EvalSymlinks(dir)
	if err != nil {
		t.Fatal(err)
	}
	return resolved + "\n" + strings.Join(args, "\n") + "\n"
}

func TestInstallUninstall(t *testing.T) {
	repo, _ := newHookRepo(t)
	hook := filepath.Join(repo, ".git", "hooks", "pre-commit")

	if code := runInstall(nil); code != 0 {
		t.Fatalf("install: exit %d", code)
	}
	first := readFile(t, hook)
	if !strings.Contains(first, preCommitHookMarker) || !strings.Contains(first, `"$pasta" -fail-on=warning`+"\n") {
		t.Fatalf("hook does not run pasta -fail-on=warning:\n%s", first)
	}
	if info, err := os.Stat(hook); err != nil || info.Mode().Perm()&0o100 == 0 {
		t.Fatalf("hook is not executable: %v", err)
	}

	if code := runInstall(nil); code != 0 {
		t.Fatalf("reinstall: exit %d", code)
	}
	if got := readFile(t, hook); got != first {
		t.Fatalf("reinstall changed the hook:\n%s", got)
	}
	if code := runInstall([]string{"-fail-on=error"}); code != 0 {
		t.Fatalf("install -fail-on=error: exit %d", code)
	}
	if got := readFile(t, hook); !strings.Contains(got, `"$pasta" -fail-on=error`+"\n") {
		t.Fatalf("hook not updated to -fail-on=error:\n%s", got)
	}

	if code := runUninstall(nil); code != 0 {
		t.Fatalf("uninstall: exit %d", code)
	}
	assertNotExist(t, hook)
	if code := runUninstall(nil); code != 0 {
		t.Fatalf("uninstall with no hook: exit %d", code)
	}
}

func TestInstall_leavesOtherHooksAlone(t *testing.T) {
	repo, _ := newHookRepo(t)
	hook := filepath.Join(repo, ".git", "hooks", "pre-commit")
	const theirs = "#!/bin/sh\nmake lint\n"
	writeFile(t, hook, theirs, 0o755)

	if code := runInstall(nil); code != 1 {
		t.Fatalf("install over another hook: exit %d, want 1", code)
	}
	if got := readFile(t, hook); got != theirs {
		t.Fatalf("install replaced another hook without -force:\n%s", got)
	}
	if code := runUninstall(nil); code != 0 {
		t.Fatalf("uninstall with another hook: exit %d", code)
	}
	if got := readFile(t, hook); got != theirs {
		t.Fatalf("uninstall touched a hook pasta didn't install:\n%s", got)
	}

	if code := runInstall([]string{"-force"}); code != 0 {
		t.Fatalf("install -force: exit %d", code)
	}
	if got := readFile(t, hook); !strings.Contains(got, preCommitHookMarker) {
		t.Fatalf("install -force didn't replace the hook:\n%s", got)
	}
}

func TestInstall_forceReplacesSymlinkNotTarget(t *testing.T) {
	repo, _ := newHookRepo(t)
	hook := filepath.Join(repo, ".git", "hooks", "pre-commit")
	target := filepath.Join(repo, "scripts", "pre-commit.sh")
	const script = "#!/bin/sh\nexit 0\n"
	writeFile(t, target, script, 0o755)
	mkdirAll(t, filepath.Dir(hook))
	if err := os.Symlink(target, hook); err != nil {
		t.Skipf("symlink not supported: %v", err)
	}

	if code := runInstall(nil); code != 1 {
		t.Fatalf("install over a symlinked hook: exit %d, want 1", code)
	}
	if code := runUninstall(nil); code != 0 {
		t.Fatalf("uninstall with a symlinked hook: exit %d", code)
	}
	if code := runInstall([]string{"-force"}); code != 0 {
		t.Fatalf("install -force: exit %d", code)
	}
	if got := readFile(t, target); got != script {
		t.Fatalf("install wrote through the symlink:\n%s", got)
	}
	if info, err := os.Lstat(hook); err != nil || !info.Mode().IsRegular() {
		t.Fatalf("hook is not a regular file: %v", err)
	}
}

func TestInstall_rulesDir(t *testing.T) {
	repo, _ := newHookRepo(t)
	hook := filepath.Join(repo, ".git", "hooks", "pre-commit")
	if err := os.Remove(filepath.Join(repo, DefaultRulesDir)); err != nil {
		t.Fatal(err)
	}

	if code := runInstall(nil); code != 2 {
		t.Fatalf("install without ./.pasta: exit %d, want 2", code)
	}
	if code := runInstall([]string{"-rules", "lint rules"}); code != 2 {
		t.Fatalf("install with a missing -rules dir: exit %d, want 2", code)
	}
	assertNotExist(t, hook)

	mkdirAll(t, filepath.Join(repo, "lint rules"))
	if code := runInstall([]string{"-rules", "lint rules"}); code != 0 {
		t.Fatalf("install -rules: exit %d", code)
	}
	if got := readFile(t, hook); !strings.Contains(got, `"$pasta" -fail-on=warning '-rules=lint rules'`+"\n") {
		t.Fatalf("hook doesn't pass -rules:\n%s", got)
	}
}

func TestInstall_outsideWorkingTree(t *testing.T) {
	isolateGit(t)
	dir := t.TempDir()
	mkdirAll(t, filepath.Join(dir, DefaultRulesDir))
	t.Setenv("GIT_CEILING_DIRECTORIES", filepath.Dir(dir))
	t.Chdir(dir)

	if code := runInstall(nil); code != 1 {
		t.Fatalf("install outside a git working tree: exit %d, want 1", code)
	}
	if code := runUninstall(nil); code != 1 {
		t.Fatalf("uninstall outside a git working tree: exit %d, want 1", code)
	}
}

func TestInstall_coreHooksPath(t *testing.T) {
	repo, _ := newHookRepo(t)
	runGit(t, repo, "config", "core.hooksPath", ".githooks")
	hook := filepath.Join(repo, ".githooks", "pre-commit")

	if code := runInstall(nil); code != 0 {
		t.Fatalf("install: exit %d", code)
	}
	if got := readFile(t, hook); !strings.Contains(got, preCommitHookMarker) {
		t.Fatalf("hook not written to core.hooksPath:\n%s", got)
	}
	assertNotExist(t, filepath.Join(repo, ".git", "hooks", "pre-commit"))

	if code := runUninstall(nil); code != 0 {
		t.Fatalf("uninstall: exit %d", code)
	}
	assertNotExist(t, hook)
}

func TestPreCommitHook_blocksCommitWhenPastaFails(t *testing.T) {
	repo, log := newHookRepo(t)
	if code := runInstall(nil); code != 0 {
		t.Fatalf("install: exit %d", code)
	}
	writeFile(t, filepath.Join(repo, "a.go"), "package a\n", 0o644)
	runGit(t, repo, "add", "a.go")

	t.Setenv("STUB_PASTA_EXIT", "1")
	commit := exec.Command("git", "commit", "--quiet", "-m", "blocked")
	commit.Dir = repo
	out, err := commit.CombinedOutput()
	if err == nil {
		t.Fatalf("commit succeeded although pasta failed:\n%s", out)
	}
	if !strings.Contains(string(out), "commit aborted") {
		t.Errorf("commit output doesn't explain the failure:\n%s", out)
	}

	t.Setenv("STUB_PASTA_EXIT", "0")
	runGit(t, repo, "commit", "--quiet", "-m", "clean")
	if got := strings.TrimSpace(runGit(t, repo, "rev-list", "--count", "HEAD")); got != "1" {
		t.Errorf("got %s commits, want 1", got)
	}
	if got, want := readFile(t, log), stubLog(t, repo, "-fail-on=warning"); got != want {
		t.Errorf("stub pasta log:\n%s\nwant:\n%s", got, want)
	}
}

func TestPreCommitHook_runsInInstallDir(t *testing.T) {
	repo, log := newHookRepo(t)
	sub := filepath.Join(repo, "sub dir")
	mkdirAll(t, filepath.Join(sub, DefaultRulesDir))
	t.Chdir(sub)
	if code := runInstall(nil); code != 0 {
		t.Fatalf("install: exit %d", code)
	}

	writeFile(t, filepath.Join(sub, "a.go"), "package a\n", 0o644)
	runGit(t, repo, "add", ".")
	runGit(t, repo, "commit", "--quiet", "-m", "x")
	if got, want := readFile(t, log), stubLog(t, sub, "-fail-on=warning"); got != want {
		t.Errorf("stub pasta log:\n%s\nwant:\n%s", got, want)
	}
}

func TestPreCommitHook_fallsBackToPath(t *testing.T) {
	repo, log := newHookRepo(t)
	sh, err := exec.LookPath("sh")
	if err != nil {
		t.Skip("sh not installed")
	}
	executable = func() (string, error) { return filepath.Join(t.TempDir(), "gone", "pasta"), nil }
	if code := runInstall(nil); code != 0 {
		t.Fatalf("install: exit %d", code)
	}
	bin := t.TempDir()
	runHook := func() (string, error) {
		cmd := exec.Command(sh, filepath.Join(repo, ".git", "hooks", "pre-commit"))
		cmd.Dir = repo
		cmd.Env = append(os.Environ(), "PATH="+bin)
		out, err := cmd.CombinedOutput()
		return string(out), err
	}

	if out, err := runHook(); err == nil || !strings.Contains(out, "pasta not found") {
		t.Fatalf("hook without pasta: err=%v\n%s", err, out)
	}
	writeStubPasta(t, filepath.Join(bin, "pasta"), log)
	if out, err := runHook(); err != nil {
		t.Fatalf("hook with pasta on PATH: %v\n%s", err, out)
	}
	if got, want := readFile(t, log), stubLog(t, repo, "-fail-on=warning"); got != want {
		t.Errorf("stub pasta log:\n%s\nwant:\n%s", got, want)
	}
}

func TestShellQuote(t *testing.T) {
	for in, want := range map[string]string{
		"-fail-on=warning":     "-fail-on=warning",
		"/usr/local/bin/pasta": "/usr/local/bin/pasta",
		"":                     "''",
		"lint rules":           "'lint rules'",
		"it's":                 `'it'\''s'`,
		"$HOME/bin":            "'$HOME/bin'",
		"~/bin":                "'~/bin'",
	} {
		if got := shellQuote(in); got != want {
			t.Errorf("shellQuote(%q) = %s, want %s", in, got, want)
		}
	}
}

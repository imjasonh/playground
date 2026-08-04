package guestinit

import (
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestArgvAndValidate(t *testing.T) {
	t.Parallel()
	s := Spec{Entrypoint: []string{"/app"}, Cmd: []string{"--ssh", ":22"}}
	got := strings.Join(Argv(s), " ")
	if got != "/app --ssh :22" {
		t.Fatalf("argv %q", got)
	}
	if err := (Spec{}).Validate(); err == nil {
		t.Fatal("expected empty spec error")
	}
	if err := s.Validate(); err != nil {
		t.Fatal(err)
	}
}

func TestSpecBeside(t *testing.T) {
	t.Parallel()
	if got := SpecBeside("/var/lib/sshcloud/fortune-rootfs.ext4"); got != "/var/lib/sshcloud/fortune-rootfs.boot.json" {
		t.Fatalf("got %q", got)
	}
	if got := SpecBeside("cached"); got != "cached.boot.json" {
		t.Fatalf("got %q", got)
	}
}

func TestWriteLoadRoundTrip(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	path := filepath.Join(dir, "boot.json")
	want := Spec{
		Entrypoint: []string{"/usr/bin/app"},
		Cmd:        []string{"-listen", ":22"},
		Env:        []string{"PATH=/bin", "FOO=bar baz"},
		WorkingDir: "/app",
	}
	if err := WriteFile(path, want); err != nil {
		t.Fatal(err)
	}
	got, err := LoadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Join(Argv(got), "\x00") != strings.Join(Argv(want), "\x00") {
		t.Fatalf("argv %+v", got)
	}
	if strings.Join(got.Env, "\x00") != strings.Join(want.Env, "\x00") || got.WorkingDir != want.WorkingDir {
		t.Fatalf("got %+v", got)
	}
}

func TestRunExecsEcho(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("exec semantics differ on windows")
	}
	echo, err := exec.LookPath("echo")
	if err != nil {
		t.Skip("echo not on PATH")
	}
	dir := t.TempDir()
	wd := filepath.Join(dir, "wd")
	if err := os.Mkdir(wd, 0o755); err != nil {
		t.Fatal(err)
	}
	specPath := filepath.Join(dir, "boot.json")
	if err := WriteFile(specPath, Spec{
		Entrypoint: []string{echo},
		Cmd:        []string{"hello-guestinit"},
		Env:        []string{"PATH=/bin:/usr/bin", "HOME=" + wd},
		WorkingDir: wd,
	}); err != nil {
		t.Fatal(err)
	}

	cmd := exec.Command("go", "run", "github.com/imjasonh/playground/sshcloud/cmd/guestinit", "-spec", specPath)
	cmd.Env = append(os.Environ(), "GOTOOLCHAIN=auto")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("guestinit: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), "hello-guestinit") {
		t.Fatalf("output %q", out)
	}
}

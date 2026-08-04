package rootfs

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestBuildFortune(t *testing.T) {
	if _, err := exec.LookPath("mkfs.ext4"); err != nil {
		t.Skip("mkfs.ext4 not available")
	}
	if _, err := exec.LookPath("debugfs"); err != nil {
		t.Skip("debugfs not available")
	}
	dir := t.TempDir()
	bin := filepath.Join(dir, "fortune")
	if err := os.WriteFile(bin, []byte("#!/bin/sh\necho hi\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	out := filepath.Join(dir, "rootfs.ext4")
	if err := BuildFortune(out, FortuneSpec{
		FortuneBin: bin,
		CAPub:      []byte("ssh-ed25519 AAAA test\n"),
		SizeMB:     8,
	}); err != nil {
		t.Fatal(err)
	}
	fi, err := os.Stat(out)
	if err != nil {
		t.Fatal(err)
	}
	if fi.Size() < 1024 {
		t.Fatalf("rootfs too small: %d", fi.Size())
	}
	// verify debugfs can see fortune
	cmd := exec.Command("debugfs", "-R", "ls -l", out)
	b, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatal(err, string(b))
	}
	if !strings.Contains(string(b), "fortune") || !strings.Contains(string(b), "ca.pub") {
		t.Fatalf("expected fortune and ca.pub in listing:\n%s", b)
	}
}

func TestBuildFromDir(t *testing.T) {
	if _, err := exec.LookPath("mkfs.ext4"); err != nil {
		t.Skip("mkfs.ext4 not available")
	}
	dir := t.TempDir()
	src := filepath.Join(dir, "src")
	if err := os.MkdirAll(filepath.Join(src, "etc"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(src, "hello"), []byte("hi\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(src, "etc", "motd"), []byte("ok\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	out := filepath.Join(dir, "rootfs.ext4")
	if err := BuildFromDir(src, out, 8); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("debugfs", "-R", "ls -l", out)
	b, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatal(err, string(b))
	}
	if !strings.Contains(string(b), "hello") || !strings.Contains(string(b), "etc") {
		t.Fatalf("expected hello and etc in listing:\n%s", b)
	}
	cmd = exec.Command("debugfs", "-R", "ls -l etc", out)
	b, err = cmd.CombinedOutput()
	if err != nil {
		t.Fatal(err, string(b))
	}
	if !strings.Contains(string(b), "motd") {
		t.Fatalf("expected motd in etc:\n%s", b)
	}
}

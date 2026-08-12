package detect

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/go-builder/internal/cnb"
)

func TestPassOnGoMod(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module example.com/hi\n\ngo 1.25\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	res, err := Run(cnb.DetectEnv{AppDir: dir, PlatformDir: dir, BuildPlanPath: filepath.Join(dir, "plan.toml")})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Pass {
		t.Fatalf("expected pass: %s", res.Reason)
	}
}

func TestFailWithoutGoMod(t *testing.T) {
	dir := t.TempDir()
	res, err := Run(cnb.DetectEnv{AppDir: dir, PlatformDir: dir, BuildPlanPath: filepath.Join(dir, "plan.toml")})
	if err != nil {
		t.Fatal(err)
	}
	if res.Pass {
		t.Fatal("expected fail")
	}
}

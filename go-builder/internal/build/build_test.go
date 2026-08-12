package build_test

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"testing"

	"github.com/imjasonh/playground/go-builder/internal/build"
	"github.com/imjasonh/playground/go-builder/internal/cnb"
	"github.com/imjasonh/playground/go-builder/internal/detect"
)

func testdata(t *testing.T, name string) string {
	t.Helper()
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("no caller")
	}
	// internal/build → ../../testdata/<name>
	dir := filepath.Join(filepath.Dir(file), "..", "..", "testdata", name)
	abs, err := filepath.Abs(dir)
	if err != nil {
		t.Fatal(err)
	}
	return abs
}

func TestBuildHello(t *testing.T) {
	app := testdata(t, "hello")
	layers := t.TempDir()
	platform := t.TempDir()
	if err := os.MkdirAll(filepath.Join(platform, "env"), 0o755); err != nil {
		t.Fatal(err)
	}

	var out bytes.Buffer
	res, err := build.Run(cnb.BuildEnv{
		LayersDir:   layers,
		PlatformDir: platform,
		AppDir:      app,
	}, build.Options{
		Stdout:                &out,
		Stderr:                &out,
		SkipToolchainDownload: true,
		GOOS:                  runtime.GOOS,
		GOARCH:                runtime.GOARCH,
	})
	if err != nil {
		t.Fatalf("build: %v\n%s", err, out.String())
	}
	if _, err := os.Stat(res.AppPath); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(res.AppPath)
	got, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(got, []byte("hello from go-builder")) {
		t.Fatalf("output: %q", got)
	}
	launch := filepath.Join(layers, "launch.toml")
	b, err := os.ReadFile(launch)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(b, []byte(res.AppPath)) {
		t.Fatalf("launch.toml missing app path:\n%s", b)
	}
}

func TestBuildKoData(t *testing.T) {
	app := testdata(t, "with-kodata")
	layers := t.TempDir()
	platform := t.TempDir()
	_ = os.MkdirAll(filepath.Join(platform, "env"), 0o755)

	var out bytes.Buffer
	res, err := build.Run(cnb.BuildEnv{
		LayersDir:   layers,
		PlatformDir: platform,
		AppDir:      app,
	}, build.Options{
		Stdout:                &out,
		Stderr:                &out,
		SkipToolchainDownload: true,
		GOOS:                  runtime.GOOS,
		GOARCH:                runtime.GOARCH,
	})
	if err != nil {
		t.Fatalf("build: %v\n%s", err, out.String())
	}
	if res.KoDataPath == "" {
		t.Fatal("expected kodata path")
	}
	msg, err := os.ReadFile(filepath.Join(res.KoDataPath, "message.txt"))
	if err != nil {
		t.Fatal(err)
	}
	if string(msg) != "kodata-ok\n" && string(msg) != "kodata-ok" {
		t.Fatalf("kodata contents: %q", msg)
	}
	cmd := exec.Command(res.AppPath)
	cmd.Env = append(os.Environ(), "KO_DATA_PATH="+res.KoDataPath)
	got, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(got, []byte("kodata-ok")) {
		t.Fatalf("output: %q", got)
	}
}

func TestBuildKoYAMLMain(t *testing.T) {
	app := testdata(t, "with-ko-yaml")
	layers := t.TempDir()
	platform := t.TempDir()
	_ = os.MkdirAll(filepath.Join(platform, "env"), 0o755)

	var out bytes.Buffer
	res, err := build.Run(cnb.BuildEnv{
		LayersDir:   layers,
		PlatformDir: platform,
		AppDir:      app,
	}, build.Options{
		Stdout:                &out,
		Stderr:                &out,
		SkipToolchainDownload: true,
		GOOS:                  runtime.GOOS,
		GOARCH:                runtime.GOARCH,
	})
	if err != nil {
		t.Fatalf("build: %v\n%s", err, out.String())
	}
	if res.Main != "./cmd/app" {
		t.Fatalf("main: %q", res.Main)
	}
	got, err := exec.Command(res.AppPath).Output()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(got, []byte("version=test")) {
		t.Fatalf("ldflags not applied: %q\n%s", got, out.String())
	}
}

func TestDetectThenBuild(t *testing.T) {
	app := testdata(t, "hello")
	platform := t.TempDir()
	plan := filepath.Join(platform, "plan.toml")
	res, err := detect.Run(cnb.DetectEnv{
		AppDir:        app,
		PlatformDir:   platform,
		BuildPlanPath: plan,
	})
	if err != nil || !res.Pass {
		t.Fatalf("detect: pass=%v err=%v", res.Pass, err)
	}
	if err := detect.WritePlan(plan, res.PlanTOML); err != nil {
		t.Fatal(err)
	}
}

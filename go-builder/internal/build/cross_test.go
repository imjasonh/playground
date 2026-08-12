package build_test

import (
	"bytes"
	"debug/buildinfo"
	"debug/elf"
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"github.com/imjasonh/playground/go-builder/internal/build"
	"github.com/imjasonh/playground/go-builder/internal/cnb"
)

func TestCrossCompileArm64(t *testing.T) {
	if runtime.GOOS != "linux" && runtime.GOOS != "darwin" {
		t.Skip("cross-compile smoke on unix only")
	}
	app := testdata(t, "hello")
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
		GOOS:                  "linux",
		GOARCH:                "arm64",
		ToolchainOS:           runtime.GOOS,
		ToolchainArch:         runtime.GOARCH,
	})
	if err != nil {
		t.Fatalf("build: %v\n%s", err, out.String())
	}

	f, err := elf.Open(res.AppPath)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if f.Machine != elf.EM_AARCH64 {
		t.Fatalf("want EM_AARCH64, got %v", f.Machine)
	}

	info, err := buildinfo.ReadFile(res.AppPath)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]string{}
	for _, s := range info.Settings {
		got[s.Key] = s.Value
	}
	if got["GOOS"] != "linux" || got["GOARCH"] != "arm64" {
		t.Fatalf("buildinfo settings: GOOS=%q GOARCH=%q", got["GOOS"], got["GOARCH"])
	}
}

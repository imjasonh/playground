package build

import (
	"runtime"
	"testing"
)

func TestResolvePlatformsDefaults(t *testing.T) {
	target, toolc := ResolvePlatforms(Options{})
	if target.OS != "linux" {
		t.Fatalf("target OS: %q", target.OS)
	}
	if target.Arch != runtime.GOARCH {
		t.Fatalf("target arch: %q", target.Arch)
	}
	if toolc.Arch != runtime.GOARCH {
		t.Fatalf("toolchain arch: %q", toolc.Arch)
	}
	// Buildpacks always run on a linux build image; darwin/windows hosts remap.
	if toolc.OS != "linux" {
		t.Fatalf("toolchain OS: %q (want linux)", toolc.OS)
	}
}

func TestResolvePlatformsCrossCompile(t *testing.T) {
	t.Setenv("CNB_TARGET_OS", "linux")
	t.Setenv("CNB_TARGET_ARCH", "arm64")
	target, toolc := ResolvePlatforms(Options{
		ToolchainOS:   "linux",
		ToolchainArch: "amd64",
	})
	if target.OS != "linux" || target.Arch != "arm64" {
		t.Fatalf("target: %+v", target)
	}
	if toolc.OS != "linux" || toolc.Arch != "amd64" {
		t.Fatalf("toolchain: %+v", toolc)
	}
}

func TestResolvePlatformsExplicitTargetWins(t *testing.T) {
	t.Setenv("CNB_TARGET_ARCH", "arm64")
	target, _ := ResolvePlatforms(Options{GOOS: "linux", GOARCH: "amd64"})
	if target.Arch != "amd64" {
		t.Fatalf("explicit GOARCH should win, got %q", target.Arch)
	}
}

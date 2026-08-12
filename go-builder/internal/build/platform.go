package build

import (
	"os"
	"runtime"
)

// Platform is the OS/arch pair for a build or toolchain.
type Platform struct {
	OS   string
	Arch string
}

// ResolvePlatforms picks:
//   - target: where the app binary will run (CNB_TARGET_*, then linux/<runtime>)
//   - toolchain: where the `go` SDK binary itself must execute (always the
//     build-container arch). Cross-compile is GOOS/GOARCH on `go build`, not
//     a foreign Go toolchain tarball.
func ResolvePlatforms(opt Options) (target, toolchain Platform) {
	target.OS = opt.GOOS
	target.Arch = opt.GOARCH
	if target.OS == "" {
		target.OS = firstNonEmpty(os.Getenv("CNB_TARGET_OS"), "linux")
	}
	if target.Arch == "" {
		target.Arch = firstNonEmpty(os.Getenv("CNB_TARGET_ARCH"), runtime.GOARCH)
	}

	toolchain.OS = firstNonEmpty(opt.ToolchainOS, runtime.GOOS)
	toolchain.Arch = firstNonEmpty(opt.ToolchainArch, runtime.GOARCH)
	// Go toolchains for containers are linux/* even when developing on Darwin —
	// the buildpack runs inside the linux build image.
	if toolchain.OS == "darwin" || toolchain.OS == "windows" {
		toolchain.OS = "linux"
	}
	return target, toolchain
}

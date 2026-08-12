// Package cnb provides small helpers for the Cloud Native Buildpacks API.
package cnb

import (
	"fmt"
	"os"
	"path/filepath"
)

// DetectEnv holds paths the platform passes to bin/detect.
type DetectEnv struct {
	PlatformDir  string
	BuildPlanPath string
	AppDir       string
	BuildpackDir string
}

// BuildEnv holds paths the platform passes to bin/build.
type BuildEnv struct {
	LayersDir    string
	PlatformDir  string
	PlanPath     string
	AppDir       string
	BuildpackDir string
}

// LoadDetectEnv reads CNB_* environment variables (API ≥ 0.9) with
// positional-arg fallbacks for older platforms.
func LoadDetectEnv(args []string) (DetectEnv, error) {
	app, err := os.Getwd()
	if err != nil {
		return DetectEnv{}, err
	}
	env := DetectEnv{
		PlatformDir:   first(os.Getenv("CNB_PLATFORM_DIR"), arg(args, 0)),
		BuildPlanPath: first(os.Getenv("CNB_BUILD_PLAN_PATH"), arg(args, 1)),
		AppDir:        first(os.Getenv("CNB_APP_DIR"), app),
		BuildpackDir:  os.Getenv("CNB_BUILDPACK_DIR"),
	}
	if env.PlatformDir == "" {
		return DetectEnv{}, fmt.Errorf("CNB_PLATFORM_DIR is required")
	}
	if env.BuildPlanPath == "" {
		return DetectEnv{}, fmt.Errorf("CNB_BUILD_PLAN_PATH is required")
	}
	if env.BuildpackDir == "" {
		// When running under `go test` / direct invocation, fall back to the
		// buildpack root (two levels up from this package is wrong); callers
		// may set it. Detect itself only needs it for metadata.
		if bp := findBuildpackRoot(); bp != "" {
			env.BuildpackDir = bp
		}
	}
	return env, nil
}

// LoadBuildEnv reads CNB_* environment variables for bin/build.
func LoadBuildEnv(args []string) (BuildEnv, error) {
	app, err := os.Getwd()
	if err != nil {
		return BuildEnv{}, err
	}
	env := BuildEnv{
		LayersDir:    first(os.Getenv("CNB_LAYERS_DIR"), arg(args, 0)),
		PlatformDir:  first(os.Getenv("CNB_PLATFORM_DIR"), arg(args, 1)),
		PlanPath:     first(os.Getenv("CNB_BP_PLAN_PATH"), arg(args, 2)),
		AppDir:       first(os.Getenv("CNB_APP_DIR"), app),
		BuildpackDir: os.Getenv("CNB_BUILDPACK_DIR"),
	}
	if env.LayersDir == "" {
		return BuildEnv{}, fmt.Errorf("CNB_LAYERS_DIR is required")
	}
	if env.PlatformDir == "" {
		return BuildEnv{}, fmt.Errorf("CNB_PLATFORM_DIR is required")
	}
	if env.BuildpackDir == "" {
		if bp := findBuildpackRoot(); bp != "" {
			env.BuildpackDir = bp
		}
	}
	return env, nil
}

// PlatformEnv returns user-provided build-time env vars from platform/env.
func PlatformEnv(platformDir string) (map[string]string, error) {
	dir := filepath.Join(platformDir, "env")
	entries, err := os.ReadDir(dir)
	if err != nil {
		if os.IsNotExist(err) {
			return map[string]string{}, nil
		}
		return nil, err
	}
	out := make(map[string]string, len(entries))
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		b, err := os.ReadFile(filepath.Join(dir, e.Name()))
		if err != nil {
			return nil, err
		}
		out[e.Name()] = string(b)
	}
	return out, nil
}

func first(values ...string) string {
	for _, v := range values {
		if v != "" {
			return v
		}
	}
	return ""
}

func arg(args []string, i int) string {
	if i >= 0 && i < len(args) {
		return args[i]
	}
	return ""
}

func findBuildpackRoot() string {
	// Walk up from cwd looking for buildpack.toml — useful in tests.
	wd, err := os.Getwd()
	if err != nil {
		return ""
	}
	dir := wd
	for {
		if _, err := os.Stat(filepath.Join(dir, "buildpack.toml")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return ""
		}
		dir = parent
	}
}

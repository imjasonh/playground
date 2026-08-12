// Package build implements the Cloud Native Buildpacks build phase for
// ko-style Go images: static compile, /ko-app binary, kodata, .ko.yaml.
package build

import (
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"

	"github.com/imjasonh/playground/go-builder/internal/cnb"
	"github.com/imjasonh/playground/go-builder/internal/config"
	"github.com/imjasonh/playground/go-builder/internal/kodata"
	"github.com/imjasonh/playground/go-builder/internal/toolchain"
)

const (
	appLayerName    = "ko-app"
	goLayerName     = "go"
	modLayerName    = "gomod"
	kodataLayerName = "kodata"

	// AppFilename is the binary name inside the launch layer (ko's default).
	AppFilename = "ko-app"
)

// Options controls build behavior (mostly for tests).
type Options struct {
	// Stdout/Stderr for go build logs; default os.Stdout/os.Stderr.
	Stdout io.Writer
	Stderr io.Writer
	// GOOS/GOARCH for the target binary; default linux/<runtime arch> for
	// buildpack builds, or runtime for local unit tests when OverrideTarget set.
	GOOS   string
	GOARCH string
	// SkipToolchainDownload forces use of host `go` only.
	SkipToolchainDownload bool
	// DefaultGoVersion from buildpack.toml metadata.
	DefaultGoVersion string
}

// Result summarizes a successful build.
type Result struct {
	AppPath      string
	KoDataPath   string
	GoVersion    string
	Main         string
	BaseImageHint string
}

// Run performs the buildpack build against env.
func Run(env cnb.BuildEnv, opt Options) (Result, error) {
	if opt.Stdout == nil {
		opt.Stdout = os.Stdout
	}
	if opt.Stderr == nil {
		opt.Stderr = os.Stderr
	}
	if opt.GOOS == "" {
		opt.GOOS = firstNonEmpty(os.Getenv("CNB_TARGET_OS"), "linux")
	}
	if opt.GOARCH == "" {
		opt.GOARCH = firstNonEmpty(os.Getenv("CNB_TARGET_ARCH"), runtime.GOARCH)
	}
	if opt.DefaultGoVersion == "" {
		opt.DefaultGoVersion = "1.25.0"
	}

	fmt.Fprintln(opt.Stdout, "---> playground/go (ko-style)")

	platformEnv, err := cnb.PlatformEnv(env.PlatformDir)
	if err != nil {
		return Result{}, err
	}
	cfg, err := config.Load(env.AppDir, platformEnv)
	if err != nil {
		return Result{}, err
	}
	if cfg.DefaultBaseImage != "" {
		fmt.Fprintf(opt.Stdout, "---> .ko.yaml defaultBaseImage=%s (builder run image is authoritative)\n", cfg.DefaultBaseImage)
	}

	hints, err := toolchain.ParseGoMod(env.AppDir)
	if err != nil {
		return Result{}, fmt.Errorf("go.mod: %w", err)
	}
	goVersion := toolchain.ResolveVersion(hints, opt.DefaultGoVersion)
	fmt.Fprintf(opt.Stdout, "---> Go toolchain %s\n", goVersion)

	goLayer, err := cnb.CreateLayer(env.LayersDir, goLayerName)
	if err != nil {
		return Result{}, err
	}
	prev, _ := cnb.ReadLayerMetadata(goLayer.Toml)
	var goBin string
	if opt.SkipToolchainDownload {
		goBin, err = exec.LookPath("go")
		if err != nil {
			return Result{}, fmt.Errorf("host go required when SkipToolchainDownload: %w", err)
		}
	} else {
		var rebuilt bool
		goBin, rebuilt, err = toolchain.Ensure(goLayer.Path, goVersion, "linux", opt.GOARCH, prev)
		if err != nil {
			return Result{}, err
		}
		if rebuilt {
			fmt.Fprintf(opt.Stdout, "---> Installed Go %s\n", goVersion)
		} else {
			fmt.Fprintf(opt.Stdout, "---> Reusing Go %s\n", goVersion)
		}
	}
	if err := cnb.WriteLayerTOML(goLayer, cnb.LayerTypes{Build: true, Cache: true}, toolchain.Metadata(goVersion, "linux", opt.GOARCH)); err != nil {
		return Result{}, err
	}
	_ = cnb.WriteLayerEnv(goLayer.Path, "PATH", filepath.Dir(goBin), "prepend")

	modLayer, err := cnb.CreateLayer(env.LayersDir, modLayerName)
	if err != nil {
		return Result{}, err
	}
	modCache := filepath.Join(modLayer.Path, "pkg", "mod")
	if err := os.MkdirAll(modCache, 0o755); err != nil {
		return Result{}, err
	}
	if err := cnb.WriteLayerTOML(modLayer, cnb.LayerTypes{Cache: true}, nil); err != nil {
		return Result{}, err
	}

	appLayer, err := cnb.CreateLayer(env.LayersDir, appLayerName)
	if err != nil {
		return Result{}, err
	}
	// Place binary at <layer>/ko-app so the launch path ends with /ko-app,
	// matching ko's binary basename convention.
	appPath := filepath.Join(appLayer.Path, AppFilename)
	if err := compile(env.AppDir, goBin, appPath, cfg, opt, modCache); err != nil {
		return Result{}, err
	}
	if err := cnb.WriteLayerTOML(appLayer, cnb.LayerTypes{Launch: true}, map[string]string{
		"main": cfg.Main,
	}); err != nil {
		return Result{}, err
	}

	launchEnv := map[string]string{}
	koDataLaunch := ""
	srcKoData, err := kodata.Find(env.AppDir, cfg.Main)
	if err != nil {
		return Result{}, err
	}
	if srcKoData != "" {
		fmt.Fprintf(opt.Stdout, "---> Bundling kodata from %s\n", srcKoData)
		kdLayer, err := cnb.CreateLayer(env.LayersDir, kodataLayerName)
		if err != nil {
			return Result{}, err
		}
		// Mirror ko's /var/run/ko layout inside the layer so relative paths match.
		dest := filepath.Join(kdLayer.Path, "var", "run", "ko")
		if err := kodata.CopyTree(srcKoData, dest); err != nil {
			return Result{}, err
		}
		if err := cnb.WriteLayerTOML(kdLayer, cnb.LayerTypes{Launch: true}, nil); err != nil {
			return Result{}, err
		}
		koDataLaunch = dest
		launchEnv["KO_DATA_PATH"] = koDataLaunch
		if err := cnb.WriteLayerEnv(kdLayer.Path, "KO_DATA_PATH", koDataLaunch, "default"); err != nil {
			return Result{}, err
		}
	}

	// Also export PATH so `ko-app` basename resolution works if someone wraps it.
	if err := cnb.WriteLayerEnv(appLayer.Path, "PATH", appLayer.Path, "prepend"); err != nil {
		return Result{}, err
	}

	if err := cnb.WriteLaunchTOML(env.LayersDir, []cnb.Process{{
		Type:    "web",
		Command: []string{appPath},
		Default: true,
	}}, launchEnv); err != nil {
		return Result{}, err
	}

	fmt.Fprintf(opt.Stdout, "---> Wrote %s\n", appPath)
	fmt.Fprintln(opt.Stdout, "---> Done")
	return Result{
		AppPath:       appPath,
		KoDataPath:    koDataLaunch,
		GoVersion:     goVersion,
		Main:          cfg.Main,
		BaseImageHint: cfg.DefaultBaseImage,
	}, nil
}

func compile(appDir, goBin, out string, cfg config.Effective, opt Options, modCache string) error {
	workDir := appDir
	if cfg.Dir != "" {
		workDir = filepath.Join(appDir, cfg.Dir)
	}
	args := []string{"build", "-o", out}
	if cfg.Trimpath {
		args = append(args, "-trimpath")
	}
	if cfg.DisableOptimizations {
		args = append(args, "-gcflags=all=-N -l")
	}
	args = append(args, cfg.Flags...)
	if len(cfg.Ldflags) > 0 {
		args = append(args, "-ldflags="+strings.Join(cfg.Ldflags, " "))
	}
	args = append(args, cfg.Main)

	cmd := exec.Command(goBin, args...)
	cmd.Dir = workDir
	cmd.Stdout = opt.Stdout
	cmd.Stderr = opt.Stderr

	env := os.Environ()
	env = setEnv(env, "CGO_ENABLED", cfg.CGOEnabled)
	env = setEnv(env, "GOOS", opt.GOOS)
	env = setEnv(env, "GOARCH", opt.GOARCH)
	env = setEnv(env, "GOMODCACHE", modCache)
	env = setEnv(env, "GOFLAGS", "") // clear hostile flags; ko rejects -toolexec etc.
	for _, e := range cfg.Env {
		k, v, ok := strings.Cut(e, "=")
		if !ok {
			continue
		}
		if k == "GOFLAGS" && strings.Contains(v, "-toolexec") {
			return fmt.Errorf("cannot set -toolexec via GOFLAGS (ko-compatible restriction)")
		}
		env = setEnv(env, k, v)
	}
	cmd.Env = env

	fmt.Fprintf(opt.Stdout, "---> Running: CGO_ENABLED=%s GOOS=%s GOARCH=%s %s %s\n",
		cfg.CGOEnabled, opt.GOOS, opt.GOARCH, goBin, strings.Join(args, " "))
	if err := cmd.Run(); err != nil {
		return fmt.Errorf("go build: %w", err)
	}
	// Ensure executable bit.
	return os.Chmod(out, 0o755)
}

func firstNonEmpty(values ...string) string {
	for _, v := range values {
		if v != "" {
			return v
		}
	}
	return ""
}

func setEnv(env []string, key, value string) []string {
	prefix := key + "="
	out := make([]string, 0, len(env)+1)
	found := false
	for _, e := range env {
		if strings.HasPrefix(e, prefix) {
			out = append(out, prefix+value)
			found = true
			continue
		}
		out = append(out, e)
	}
	if !found {
		out = append(out, prefix+value)
	}
	return out
}

package buildcmd

import (
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/imjasonh/playground/node-image/internal/app"
	"github.com/imjasonh/playground/node-image/internal/config"
	"github.com/imjasonh/playground/node-image/internal/fetch"
	"github.com/imjasonh/playground/node-image/internal/layer"
	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/publish"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

// Options are CLI-facing build options (override config).
type Options struct {
	Dir       string
	Repo      string
	Base      string
	Platforms []string
	Tags      []string
	SkipBuild bool
	NoPush    bool
	OCIDir    string
	EmptyBase bool
	Stdout    io.Writer
	Stderr    io.Writer
}

// Run executes a build and returns the image reference / digest string.
func Run(opt Options) (string, error) {
	stdout := opt.Stdout
	if stdout == nil {
		stdout = os.Stdout
	}
	stderr := opt.Stderr
	if stderr == nil {
		stderr = os.Stderr
	}
	dir := opt.Dir
	if dir == "" {
		dir = "."
	}
	cfg, _, err := config.Load(dir)
	if err != nil {
		return "", err
	}
	if opt.Repo != "" {
		cfg.Repo = opt.Repo
	}
	if opt.Base != "" {
		cfg.Base = opt.Base
	}
	if len(opt.Platforms) > 0 {
		cfg.Platforms = opt.Platforms
	}
	if len(opt.Tags) > 0 {
		cfg.Tags = opt.Tags
	}
	cfg.SkipBuild = opt.SkipBuild
	cfg.NoPush = opt.NoPush
	cfg.OCIDir = opt.OCIDir

	if !cfg.NoPush && cfg.Repo == "" {
		return "", fmt.Errorf("--repo is required unless --no-push")
	}

	lockPath, lockRoot, err := lock.FindLockfile(cfg.Dir)
	if err != nil {
		return "", err
	}
	l, err := lock.ParseFile(lockPath)
	if err != nil {
		return "", err
	}
	importer, err := lock.ImporterKey(lockRoot, cfg.Dir)
	if err != nil {
		return "", err
	}

	if !cfg.SkipBuild && cfg.BuildScript != "" {
		fmt.Fprintf(stderr, "compiling with pnpm run %s\n", cfg.BuildScript)
		if err := app.Compile(cfg.Dir, lockRoot, cfg.BuildScript); err != nil {
			return "", err
		}
	}

	cacheDir, err := fetch.DefaultDir()
	if err != nil {
		return "", err
	}
	cache := &fetch.Cache{Dir: cacheDir}

	platforms := cfg.Platforms
	if len(platforms) == 0 {
		platforms = []string{"linux/amd64"}
	}

	stageRoot := filepath.Join(os.TempDir(), fmt.Sprintf("node-image-%d", os.Getpid()))
	defer os.RemoveAll(stageRoot)

	var built []publish.PlatformImage
	for _, pstr := range platforms {
		plat, err := publish.ParsePlatform(pstr)
		if err != nil {
			return "", err
		}
		rplat := resolve.Platform{
			OS:   plat.OS,
			CPU:  publish.ResolveCPU(plat.Architecture),
			Libc: "glibc",
		}
		refs, err := resolve.Closure(l, importer, rplat)
		if err != nil {
			return "", err
		}
		tarballs := map[string]string{}
		for _, ref := range refs {
			path, err := cache.Ensure(ref.Tarball, ref.Integrity)
			if err != nil {
				return "", err
			}
			tarballs[ref.PackageID] = path
		}

		stage := filepath.Join(stageRoot, strings.ReplaceAll(pstr, "/", "-"))
		if err := os.MkdirAll(stage, 0o755); err != nil {
			return "", err
		}
		if _, err := layout.Materialize(stage, l, refs, tarballs); err != nil {
			return "", err
		}

		outputs, err := app.CollectOutputs(cfg.Dir)
		if err != nil {
			return "", err
		}
		for rel, src := range outputs {
			dst := filepath.Join(stage, filepath.FromSlash(rel))
			if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
				return "", err
			}
			if err := copyFile(src, dst); err != nil {
				return "", err
			}
		}

		storeFiles, linkFiles, appFiles, err := splitLayers(stage)
		if err != nil {
			return "", err
		}
		prefix := strings.TrimPrefix(cfg.Workdir, "/")
		layers := []publish.LayerFiles{
			{Files: prefixFiles(prefix, storeFiles)},
			{Files: prefixFiles(prefix, linkFiles)},
			{Files: prefixFiles(prefix, appFiles)},
		}
		popts := publish.Options{
			Base:       cfg.Base,
			Workdir:    cfg.Workdir,
			User:       cfg.User,
			Entrypoint: cfg.Entrypoint,
			Cmd:        cfg.Cmd(),
			Platform:   plat,
		}

		var image v1.Image
		if opt.EmptyBase || cfg.Base == "scratch" {
			image, err = publish.EmptyImage(popts, layers)
		} else {
			image, err = publish.BuildImage(popts, layers)
		}
		if err != nil {
			return "", err
		}
		built = append(built, publish.PlatformImage{Platform: plat, Image: image})
	}

	var lastRef string
	if len(built) == 1 {
		image := built[0].Image
		if cfg.NoPush {
			outDir := cfg.OCIDir
			if outDir == "" {
				outDir = filepath.Join(cfg.Dir, ".node-image-out")
			}
			dig, err := publish.WriteDigestSummary(outDir, image)
			if err != nil {
				return "", err
			}
			fmt.Fprintf(stderr, "wrote %s (%s)\n", outDir, dig)
			lastRef = dig
		} else {
			ref, err := publish.Push(cfg.Repo, cfg.Tags, image)
			if err != nil {
				return "", err
			}
			lastRef = ref
		}
	} else {
		idx, err := publish.MakeIndex(built)
		if err != nil {
			return "", err
		}
		if cfg.NoPush {
			outDir := cfg.OCIDir
			if outDir == "" {
				outDir = filepath.Join(cfg.Dir, ".node-image-out")
			}
			dig, err := publish.WriteIndexSummary(outDir, idx)
			if err != nil {
				return "", err
			}
			fmt.Fprintf(stderr, "wrote multi-arch index %s (%s)\n", outDir, dig)
			lastRef = dig
		} else {
			ref, err := publish.PushIndex(cfg.Repo, cfg.Tags, idx)
			if err != nil {
				return "", err
			}
			lastRef = ref
		}
	}

	fmt.Fprintln(stdout, lastRef)
	return lastRef, nil
}

func copyFile(src, dst string) error {
	in, err := os.ReadFile(src)
	if err != nil {
		return err
	}
	return os.WriteFile(dst, in, 0o644)
}

func prefixFiles(prefix string, files []layer.File) []layer.File {
	if prefix == "" {
		return files
	}
	out := make([]layer.File, len(files))
	for i, f := range files {
		f.Rel = prefix + "/" + f.Rel
		out[i] = f
	}
	return out
}

func splitLayers(stage string) (store, links, appFiles []layer.File, err error) {
	nm := filepath.Join(stage, "node_modules")
	pnpmDir := filepath.Join(nm, ".pnpm")
	if st, e := os.Stat(pnpmDir); e == nil && st.IsDir() {
		store, err = layer.FromDir(pnpmDir, "node_modules/.pnpm")
		if err != nil {
			return nil, nil, nil, err
		}
	}
	entries, err := os.ReadDir(nm)
	if err != nil {
		return nil, nil, nil, err
	}
	for _, e := range entries {
		name := e.Name()
		if name == ".pnpm" || name == ".modules.yaml" || strings.HasPrefix(name, ".pnpm-") {
			continue
		}
		p := filepath.Join(nm, name)
		info, err := os.Lstat(p)
		if err != nil {
			return nil, nil, nil, err
		}
		rel := "node_modules/" + name
		if info.Mode()&os.ModeSymlink != 0 {
			target, err := os.Readlink(p)
			if err != nil {
				return nil, nil, nil, err
			}
			links = append(links, layer.File{Rel: rel, Mode: fs.ModeSymlink | 0o777, Link: filepath.ToSlash(target)})
			continue
		}
		if info.IsDir() {
			sub, err := layer.FromDir(p, rel)
			if err != nil {
				return nil, nil, nil, err
			}
			links = append(links, sub...)
			continue
		}
		b, err := os.ReadFile(p)
		if err != nil {
			return nil, nil, nil, err
		}
		links = append(links, layer.File{Rel: rel, Mode: 0o644, Body: b})
	}

	err = filepath.Walk(stage, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(stage, path)
		if rel == "." {
			return nil
		}
		rel = filepath.ToSlash(rel)
		if rel == "node_modules" || strings.HasPrefix(rel, "node_modules/") {
			if info.IsDir() && rel == "node_modules" {
				return filepath.SkipDir
			}
			return nil
		}
		if info.IsDir() {
			appFiles = append(appFiles, layer.File{Rel: rel, Mode: fs.ModeDir | 0o755})
			return nil
		}
		if info.Mode()&os.ModeSymlink != 0 {
			target, err := os.Readlink(path)
			if err != nil {
				return err
			}
			appFiles = append(appFiles, layer.File{Rel: rel, Mode: fs.ModeSymlink | 0o777, Link: filepath.ToSlash(target)})
			return nil
		}
		b, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		mode := info.Mode().Perm()
		if mode&0o111 != 0 {
			mode = 0o755
		} else {
			mode = 0o644
		}
		appFiles = append(appFiles, layer.File{Rel: rel, Mode: mode, Body: b})
		return nil
	})
	return store, links, appFiles, err
}

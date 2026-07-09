package buildcmd

import (
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/imjasonh/playground/node-image/internal/app"
	"github.com/imjasonh/playground/node-image/internal/base"
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
	Local     bool // load into local Docker daemon (ko-style -L)
	OCIDir    string
	EmptyBase bool
	MaxLayers int // 0 = use config default
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
	cfg.Local = opt.Local
	cfg.OCIDir = opt.OCIDir
	if opt.MaxLayers > 0 {
		cfg.MaxLayers = opt.MaxLayers
	}

	if cfg.Local && cfg.NoPush {
		return "", fmt.Errorf("--local and --no-push are mutually exclusive\nHint: use --local (-L) to load into Docker, or --no-push for a digest summary")
	}
	if !cfg.NoPush && !cfg.Local && cfg.Repo == "" {
		return "", fmt.Errorf("--repo is required to push an image\nHint: pass --repo registry.example.com/my/app, use --local (-L) to load into Docker, or --no-push --oci-dir /tmp/out for a digest summary")
	}
	if cfg.Local && cfg.Repo == "" {
		cfg.Repo = "app"
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
	if l.Importers[importer] == nil {
		return "", fmt.Errorf("importer %q not found in %s\nHint: the package directory must be a workspace member (or .) relative to the lockfile root %s", importer, lockPath, lockRoot)
	}

	if !cfg.SkipBuild && cfg.BuildScript != "" {
		fmt.Fprintf(stderr, "compiling with pnpm run %s\n", cfg.BuildScript)
		if err := app.Compile(cfg.Dir, lockRoot, cfg.BuildScript); err != nil {
			return "", err
		}
	}

	// Resolve the JS entrypoint after compile so dist/ exists for TypeScript apps
	// whose package.json#main still points at a .ts source file.
	if len(cfg.CmdOverride) == 0 {
		resolved, err := config.ResolveMain(cfg.Dir, cfg.Main, cfg.BuildScript != "")
		if err != nil {
			return "", err
		}
		if resolved != cfg.Main && cfg.Main != "" {
			fmt.Fprintf(stderr, "entrypoint: using %s (package.json main was %q)\n", resolved, cfg.Main)
		}
		cfg.Main = resolved
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

	// Inspect base once (first platform) for libc/Node/layer budget unless empty-base.
	var baseInfo *base.Info
	if opt.EmptyBase || cfg.Base == "scratch" {
		baseInfo = base.ScratchInfo()
	} else {
		firstPlat, err := publish.ParsePlatform(platforms[0])
		if err != nil {
			return "", err
		}
		baseInfo, err = base.Inspect(cfg.Base, firstPlat)
		if err != nil {
			return "", err
		}
		if err := base.RequireGlibc(baseInfo); err != nil {
			return "", err
		}
		if err := base.CheckEngines(cfg.EnginesNode, baseInfo); err != nil {
			return "", err
		}
		for _, w := range baseInfo.Warnings {
			fmt.Fprintf(stderr, "warning: %s\n", w)
		}
	}

	spoolRoot, err := layout.SpoolDir()
	if err != nil {
		return "", err
	}
	blobCacheDir, err := layer.DefaultBlobCacheDir()
	if err != nil {
		return "", err
	}
	blobCache := &layer.BlobCache{Dir: blobCacheDir}

	var built []publish.PlatformImage
	for _, pstr := range platforms {
		plat, err := publish.ParsePlatform(pstr)
		if err != nil {
			return "", fmt.Errorf("invalid --platform %q: %w\nHint: use forms like linux/amd64 or linux/arm64", pstr, err)
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
		direct := resolve.DirectDeps(l, importer)
		tarballs := map[string]string{}
		integrityKeys := map[string]string{}
		for _, ref := range refs {
			path, err := cache.Ensure(ref.Tarball, ref.Integrity)
			if err != nil {
				return "", fmt.Errorf("fetch %s: %w\nHint: check network access to the npm registry and that the integrity in pnpm-lock.yaml is current", ref.PackageID, err)
			}
			tarballs[ref.PackageID] = path
			key, err := fetch.IntegrityKey(ref.Integrity)
			if err != nil {
				return "", err
			}
			integrityKeys[ref.PackageID] = key
		}

		planned, err := layout.PlanLayout(l, refs, tarballs, direct, layout.PlanOptions{
			SpoolRoot:    spoolRoot,
			IntegrityKey: integrityKeys,
		})
		if err != nil {
			return "", err
		}

		outputs, err := app.CollectOutputs(cfg.Dir)
		if err != nil {
			return "", err
		}
		if err := app.RequireMain(cfg.Dir, cfg.Main, outputs); err != nil {
			return "", err
		}
		appFiles := appLayerFiles(outputs)

		layers, err := assemblePlannedLayers(planned, appFiles, cfg, baseInfo, stderr)
		if err != nil {
			return "", err
		}
		popts := publish.Options{
			Base:       cfg.Base,
			Workdir:    cfg.Workdir,
			User:       cfg.User,
			Entrypoint: cfg.Entrypoint,
			Cmd:        cfg.Cmd(),
			Env:        cfg.EnvList(),
			Platform:   plat,
			BlobCache:  blobCache,
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
		switch {
		case cfg.NoPush:
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
		case cfg.Local:
			ref, err := publish.LoadLocal(cfg.Repo, cfg.Tags, image)
			if err != nil {
				return "", err
			}
			lastRef = ref
		default:
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
		switch {
		case cfg.NoPush:
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
		case cfg.Local:
			return "", fmt.Errorf("--local does not support multi-arch indexes (Docker daemon loads a single image)\nHint: pass --platform linux/%s (or one arch) with -L", hostArchHint())
		default:
			ref, err := publish.PushIndex(cfg.Repo, cfg.Tags, idx)
			if err != nil {
				return "", err
			}
			lastRef = ref
		}
	}

	// Contract: stdout is exactly one line — the fully resolved image ref —
	// so `docker run --rm $(node-image build …)` works. Progress goes to stderr.
	fmt.Fprintln(stdout, lastRef)
	return lastRef, nil
}

func hostArchHint() string {
	if runtime.GOARCH == "arm64" {
		return "arm64"
	}
	return "amd64"
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

func assemblePlannedLayers(planned *layout.PlannedLayout, appFiles []layer.File, cfg *config.Config, baseInfo *base.Info, stderr io.Writer) ([]publish.LayerFiles, error) {
	budget := layer.Budget{
		MaxLayers:   cfg.MaxLayers,
		BaseLayers:  baseInfo.LayerCount,
		ExtraLayers: 2, // symlink + app
	}
	slots := budget.StoreSlots()
	if len(planned.Store) > slots {
		fmt.Fprintf(stderr, "layer budget: %d store packages into %d buckets (max-layers=%d, base=%d, extra=2)\n",
			len(planned.Store), slots, cfg.MaxLayers, baseInfo.LayerCount)
	}
	storeGroups := layer.BucketStorePackages(planned.Store, slots)
	prefix := strings.TrimPrefix(cfg.Workdir, "/")
	out := make([]publish.LayerFiles, 0, len(storeGroups)+2)
	for _, g := range storeGroups {
		out = append(out, publish.LayerFiles{Files: prefixFiles(prefix, g)})
	}
	out = append(out,
		publish.LayerFiles{Files: prefixFiles(prefix, planned.Links)},
		publish.LayerFiles{Files: prefixFiles(prefix, appFiles)},
	)
	return out, nil
}

// appLayerFiles turns CollectOutputs (rel → abs source) into layer files that
// stream from DiskPath — no staging copy.
func appLayerFiles(outputs map[string]string) []layer.File {
	rels := make([]string, 0, len(outputs))
	for rel := range outputs {
		rels = append(rels, rel)
	}
	sort.Strings(rels)
	var files []layer.File
	seenDir := map[string]struct{}{}
	for _, rel := range rels {
		src := outputs[rel]
		// Ensure parent dir entries exist in the layer.
		parts := strings.Split(rel, "/")
		cur := ""
		for _, p := range parts[:len(parts)-1] {
			if cur == "" {
				cur = p
			} else {
				cur += "/" + p
			}
			if _, ok := seenDir[cur]; ok {
				continue
			}
			seenDir[cur] = struct{}{}
			files = append(files, layer.File{Rel: cur, Mode: fs.ModeDir | 0o755})
		}
		mode := fs.FileMode(0o644)
		if st, err := os.Stat(src); err == nil {
			if st.Mode().Perm()&0o111 != 0 {
				mode = 0o755
			}
		}
		files = append(files, layer.File{Rel: rel, Mode: mode, DiskPath: src})
	}
	return files
}

package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"net/url"
	"os"
	"path"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"chainguard.dev/apko/pkg/build/oci"
	"chainguard.dev/apko/pkg/build/types"
	"chainguard.dev/apko/pkg/lock"
	"github.com/containerd/platforms"
	"github.com/distribution/reference"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/moby/buildkit/client/llb"
	"github.com/moby/buildkit/client/llb/sourceresolver"
	"github.com/moby/buildkit/exporter/containerimage/exptypes"
	"github.com/moby/buildkit/frontend/dockerui"
	"github.com/moby/buildkit/frontend/gateway/client"
	"github.com/moby/buildkit/solver/pb"
	dockerspec "github.com/moby/docker-image-spec/specs-go/v1"
	ocispecs "github.com/opencontainers/image-spec/specs-go/v1"
)

const (
	// argLock names a build argument with the path of an apko lock file in
	// the build context. When set, the frontend installs the locked
	// packages instead of resolving the configuration.
	argLock = "APKO_LOCK"
	// argSourceDateEpoch is the standard build argument for reproducible
	// timestamps. apko reads the same variable.
	argSourceDateEpoch = "SOURCE_DATE_EPOCH"
)

// builder holds what every platform's build shares.
type builder struct {
	c       client.Client
	fetcher *fetcher
	// rec recorded the URLs apko fetched while resolving packages.
	rec *recorder
	// ic is the configuration as written.
	ic types.ImageConfiguration
	// locked holds each arch's pinned configuration.
	locked map[types.Architecture]*locked
	// localInputs lists the build-context files apko read while
	// resolving. The helper needs the keyring files among them.
	localInputs []string
	// mainContext returns the build context, limited to the given paths.
	mainContext func(ctx context.Context, paths ...string) (llb.State, error)
	// helper runs this binary, exe, on the build platform.
	helper llb.State
	exe    string
	epoch  string
	// proxy holds the proxy build arguments for the fetch steps. BuildKit
	// leaves them out of the steps' cache keys.
	proxy llb.ProxyEnv
	// cacheImports are the client's --cache-from caches. A frontend's
	// solves use them only when it passes them along.
	cacheImports []client.CacheOptionsEntry
}

// frontendBuild is the frontend's entry point.
func frontendBuild(ctx context.Context, c client.Client) (*client.Result, error) {
	dc, err := dockerui.NewClient(c)
	if err != nil {
		return nil, err
	}
	src, err := dc.ReadEntrypoint(ctx, "YAML")
	if err != nil {
		return nil, err
	}
	ic, err := parseConfig(src.Data)
	if err != nil {
		return nil, err
	}
	for _, k := range ic.Contents.Keyring {
		if strings.HasPrefix(k, "http://") {
			src.Warn(ctx, "keyring "+k+" is fetched without TLS; every signature check trusts this key, so use https",
				client.WarnOpts{Range: lineRange(src.Data, k)})
		}
	}
	b := &builder{c: c, ic: ic, epoch: dc.BuildArgs[argSourceDateEpoch], proxy: proxyEnv(dc.BuildArgs), cacheImports: dc.CacheImports}
	if b.epoch != "" {
		if _, err := strconv.ParseInt(b.epoch, 10, 64); err != nil {
			return nil, fmt.Errorf("invalid %s %q: %w", argSourceDateEpoch, b.epoch, err)
		}
	}
	if b.helper, b.exe, err = helperImage(ctx, c, dc); err != nil {
		return nil, err
	}
	b.mainContext = func(ctx context.Context, paths ...string) (llb.State, error) {
		st, err := dc.MainContext(ctx, llb.FollowPaths(paths))
		if err != nil {
			return llb.State{}, err
		}
		return *st, nil
	}
	b.fetcher = newFetcher(c, b.mainContext, func(msg string) {
		src.Warn(ctx, msg, client.WarnOpts{})
	})
	b.rec = b.fetcher.recorder()

	if len(dc.TargetPlatforms) == 0 {
		ps := configPlatforms(ic)
		for _, p := range ps {
			dc.TargetPlatforms = append(dc.TargetPlatforms, specPlatform(p))
		}
		dc.MultiPlatformRequested = len(ps) > 1
	}
	var archs []types.Architecture
	for _, p := range dc.TargetPlatforms {
		archs = append(archs, platformArch(ggcrPlatform(p)))
	}
	if len(archs) == 0 {
		archs = append(archs, platformArch(ggcrPlatform(platforms.DefaultSpec())))
	}

	if b.localInputs, err = localInputs(ic, archs); err != nil {
		return nil, err
	}
	if len(b.localInputs) > 0 {
		if err := b.stage(ctx, b.localInputs); err != nil {
			return nil, err
		}
	}
	if p := dc.BuildArgs[argLock]; p != "" {
		e, err := b.fetcher.entry(ctx, contextURL(p))
		if err != nil {
			return nil, err
		}
		data, err := b.fetcher.get(ctx, e)
		if err != nil {
			return nil, fmt.Errorf("reading %s %s: %w", argLock, p, err)
		}
		l, err := parseLock(data)
		if err != nil {
			return nil, err
		}
		b.locked, err = fromLock(ctx, ic, archs, l, data, b.rec)
		if err != nil {
			return nil, err
		}
	} else if b.locked, err = resolve(ctx, ic, archs, b.rec); err != nil {
		return nil, err
	}

	type platformAnnotations struct {
		platform    ocispecs.Platform
		annotations map[string]string
	}
	var mu sync.Mutex
	var annotations []platformAnnotations
	rb, err := dc.Build(ctx, func(ctx context.Context, sp *ocispecs.Platform, _ int) (*dockerui.BuildResult, error) {
		// dockerui exports a nil platform as the default platform.
		if sp == nil {
			def := platforms.DefaultSpec()
			sp = &def
		}
		p := ggcrPlatform(*sp)
		res, anns, err := b.buildPlatform(ctx, p)
		if err != nil {
			return nil, fmt.Errorf("building %s: %w", p, err)
		}
		mu.Lock()
		defer mu.Unlock()
		annotations = append(annotations, platformAnnotations{*sp, anns})
		return res, nil
	})
	if err != nil {
		return nil, err
	}
	for _, pa := range annotations {
		for k, v := range pa.annotations {
			key := exptypes.AnnotationKey{Type: exptypes.AnnotationManifest, Key: k}
			if dc.MultiPlatformRequested {
				key.Platform = &pa.platform
			}
			rb.AddMeta(key.String(), []byte(v))
		}
	}
	if dc.MultiPlatformRequested {
		for k, v := range ic.Annotations {
			rb.AddMeta(exptypes.AnnotationKey{Type: exptypes.AnnotationIndex, Key: k}.String(), []byte(v))
		}
	}
	return rb.Finalize()
}

// helperImage returns this frontend's own image, pinned by digest, for the
// build platform, and the path of this binary inside it. BuildKit passes the
// frontend image reference as the "source" option.
func helperImage(ctx context.Context, c client.Client, dc *dockerui.Client) (llb.State, string, error) {
	source := c.BuildOpts().Opts["source"]
	if source == "" {
		return llb.State{}, "", errors.New(`the frontend image is unknown; run this frontend with "# syntax=<image>" or the gateway.v0 frontend's source option`)
	}
	exe, err := os.Executable()
	if err != nil {
		return llb.State{}, "", err
	}
	bp := platforms.DefaultSpec()
	if len(dc.BuildPlatforms) > 0 {
		bp = dc.BuildPlatforms[0]
	}
	named, err := reference.ParseNormalizedNamed(source)
	if err != nil {
		return llb.State{}, "", fmt.Errorf("parsing frontend image %s: %w", source, err)
	}
	_, dgst, _, err := c.ResolveImageConfig(ctx, reference.TagNameOnly(named).String(), sourceresolver.Opt{
		ImageOpt: &sourceresolver.ResolveImageOpt{Platform: &bp},
	})
	if err != nil {
		return llb.State{}, "", fmt.Errorf("resolving frontend image %s: %w", source, err)
	}
	pinned, err := reference.WithDigest(reference.TrimNamed(named), dgst)
	if err != nil {
		return llb.State{}, "", err
	}
	return llb.Image(pinned.String(), llb.Platform(bp)), exe, nil
}

// buildPlatform builds the image for one platform and returns it with the
// manifest annotations apko would set.
func (b *builder) buildPlatform(ctx context.Context, p v1.Platform) (*dockerui.BuildResult, map[string]string, error) {
	arch := platformArch(p)
	lk, ok := b.locked[arch]
	if !ok {
		return nil, nil, fmt.Errorf("no packages were resolved for %s", arch)
	}
	// The helper installs from a lock, so it needs the keys apko fetched
	// but not the indexes. Leaving the indexes out keeps the helper's
	// cache key unchanged when an index changes but the packages don't.
	fetched := map[string]llb.State{}
	for key, e := range b.rec.entries() {
		if path.Base(e.url) != "APKINDEX.tar.gz" {
			fetched[key] = e.state
		}
	}
	var localPaths []string
	for _, p := range b.localInputs {
		if path.Base(p) != "APKINDEX.tar.gz" {
			localPaths = append(localPaths, p)
		}
	}
	for _, pkg := range lk.pkgs {
		if !isRemote(pkg.URL) {
			p, err := contextPath(pkg.URL)
			if err != nil {
				return nil, nil, err
			}
			localPaths = append(localPaths, p)
			continue
		}
		key, err := fetchKey(pkg.URL)
		if err != nil {
			return nil, nil, err
		}
		fetched[key] = b.fetchPackage(pkg, key)
	}

	configData, err := json.Marshal(lk.ic)
	if err != nil {
		return nil, nil, err
	}
	input := llb.Scratch().File(
		llb.Mkfile("/config.json", 0o644, configData).
			Mkfile("/lock.json", 0o644, lk.lockData),
		llb.WithCustomName("[internal] apko configuration and lock"),
	)
	runOpts := []llb.RunOption{
		llb.Args([]string{
			b.exe, helperCommand,
			"-arch", arch.ToAPK(),
			"-config", "/apko/in/config.json",
			"-lock", "/apko/in/lock.json",
			"-fetch", "/apko/fetch",
			"-out", "/apko/out",
		}),
		llb.User("0"),
		llb.Network(llb.NetModeNone),
		llb.AddMount("/apko/in", input, llb.Readonly),
		llb.AddMount("/apko/fetch", mergeStates(sortedStates(fetched), "fetched files"), llb.Readonly),
		llb.WithCustomNamef("apko build %s (%d packages)", arch.ToAPK(), len(lk.pkgs)),
	}
	if b.epoch != "" {
		runOpts = append(runOpts, llb.AddEnv(argSourceDateEpoch, b.epoch))
	}
	if len(localPaths) > 0 {
		slices.Sort(localPaths)
		src, err := b.mainContext(ctx, slices.Compact(localPaths)...)
		if err != nil {
			return nil, nil, err
		}
		runOpts = append(runOpts, llb.AddMount(contextDir, src, llb.Readonly), llb.Dir(contextDir))
	}
	out := b.helper.Run(runOpts...).AddMount("/apko/out", llb.Scratch())

	pl, err := b.readPlan(ctx, out)
	if err != nil {
		return nil, nil, err
	}
	layers := make([]llb.State, 0, len(pl.Layers))
	for i, l := range pl.Layers {
		layers = append(layers, llb.Scratch().File(
			llb.Copy(out, "/"+l.File, "/", &llb.CopyInfo{AttemptUnpack: true}),
			llb.WithCustomName(layerName(arch, i, len(pl.Layers), l)),
		))
	}
	def, err := mergeStates(layers, "apko layers "+arch.ToAPK()).Marshal(ctx, llb.Platform(specPlatform(p)))
	if err != nil {
		return nil, nil, err
	}
	res, err := b.c.Solve(ctx, client.SolveRequest{Definition: def.ToPB(), CacheImports: b.cacheImports})
	if err != nil {
		return nil, nil, err
	}
	ref, err := res.SingleRef()
	if err != nil {
		return nil, nil, err
	}
	img, anns, err := imageConfig(ctx, b.ic, arch, pl.Created, len(pl.Layers))
	if err != nil {
		return nil, nil, err
	}
	created := pl.Created
	return &dockerui.BuildResult{Reference: ref, Image: img, Epoch: &created}, anns, nil
}

// fetchPackage returns a state whose root holds the package pkg in a file
// named key. A build step downloads it and checks it against the lock's
// checksum, which came from a signed index. Unlike an HTTP source, the
// step's cache key doesn't depend on the file's content, so BuildKit can
// find a cached apko step, locally or in a remote cache, without
// downloading the packages.
//
// The step mounts the same optional secrets that BuildKit's HTTP source
// reads for the package's host, HTTP_AUTH_HEADER_<host> and
// HTTP_AUTH_TOKEN_<host>, so one --secret authenticates both the index
// fetches and the downloads. Secrets aren't part of the cache key.
func (b *builder) fetchPackage(pkg lock.LockPkg, key string) llb.State {
	var host string
	if u, err := url.Parse(pkg.URL); err == nil {
		host = u.Hostname()
	}
	return b.helper.Run(
		llb.Args([]string{
			b.exe, fetchCommand,
			"-url", pkg.URL,
			"-checksum", pkg.Checksum,
			"-auth-header-file", authHeaderFile,
			"-auth-token-file", authTokenFile,
			"-out", "/out/" + key,
		}),
		llb.User("0"),
		llb.WithProxy(b.proxy),
		llb.AddSecret(authHeaderFile, llb.SecretID(authHeaderSecretPrefix+host), llb.SecretOptional),
		llb.AddSecret(authTokenFile, llb.SecretID(authTokenSecretPrefix+host), llb.SecretOptional),
		llb.WithCustomNamef("fetch %s", redactURL(pkg.URL)),
	).AddMount("/out", llb.Scratch())
}

const (
	// authHeaderSecretPrefix and authTokenSecretPrefix name the secrets
	// that BuildKit's HTTP source reads for a host: the whole
	// Authorization header, or a token to send as "Bearer <token>".
	authHeaderSecretPrefix = "HTTP_AUTH_HEADER_"
	authTokenSecretPrefix  = "HTTP_AUTH_TOKEN_"

	authHeaderFile = "/run/secrets/http-auth-header"
	authTokenFile  = "/run/secrets/http-auth-token"
)

// sortedStates returns the states sorted by key, so the build definition
// doesn't depend on map order.
func sortedStates(states map[string]llb.State) []llb.State {
	out := make([]llb.State, 0, len(states))
	for _, k := range slices.Sorted(maps.Keys(states)) {
		out = append(out, states[k])
	}
	return out
}

func redactURL(raw string) string {
	u, err := url.Parse(raw)
	if err != nil {
		return raw
	}
	return u.Redacted()
}

func (b *builder) readPlan(ctx context.Context, out llb.State) (*plan, error) {
	def, err := out.Marshal(ctx)
	if err != nil {
		return nil, err
	}
	res, err := b.c.Solve(ctx, client.SolveRequest{Definition: def.ToPB(), CacheImports: b.cacheImports})
	if err != nil {
		return nil, err
	}
	ref, err := res.SingleRef()
	if err != nil {
		return nil, err
	}
	data, err := ref.ReadFile(ctx, client.ReadRequest{Filename: planFile})
	if err != nil {
		return nil, err
	}
	var pl plan
	if err := json.Unmarshal(data, &pl); err != nil {
		return nil, fmt.Errorf("parsing %s: %w", planFile, err)
	}
	if len(pl.Layers) == 0 {
		return nil, errors.New("the apko build wrote no layers")
	}
	return &pl, nil
}

func layerName(arch types.Architecture, i, n int, l planLayer) string {
	what := "accounts, paths, and apk database"
	if len(l.Packages) > 0 {
		what = strings.Join(l.Packages, ", ")
		if len(what) > 80 {
			what = what[:77] + "..."
		}
	} else if n == 1 {
		what = "all packages"
	}
	return fmt.Sprintf("apko layer %s %d/%d: %s", arch.ToAPK(), i+1, n, what)
}

// proxyEnv returns the proxy settings from the standard proxy build
// arguments, which Docker sets from the client's proxy configuration.
func proxyEnv(args map[string]string) llb.ProxyEnv {
	get := func(name string) string {
		if v := args[name]; v != "" {
			return v
		}
		return args[strings.ToLower(name)]
	}
	return llb.ProxyEnv{
		HTTPProxy:  get("HTTP_PROXY"),
		HTTPSProxy: get("HTTPS_PROXY"),
		FTPProxy:   get("FTP_PROXY"),
		NoProxy:    get("NO_PROXY"),
		AllProxy:   get("ALL_PROXY"),
	}
}

// lineRange returns the range of the first line of data that contains s, for
// pointing a warning at it.
func lineRange(data []byte, s string) []*pb.Range {
	for i, line := range strings.Split(string(data), "\n") {
		if strings.Contains(line, s) {
			pos := &pb.Position{Line: int32(i + 1)}
			return []*pb.Range{{Start: pos, End: pos}}
		}
	}
	return nil
}

// mergeStates merges states, or returns the only state.
func mergeStates(states []llb.State, name string) llb.State {
	switch len(states) {
	case 0:
		return llb.Scratch()
	case 1:
		return states[0]
	}
	return llb.Merge(states, llb.WithCustomName(name))
}

// imageConfig returns the image config and manifest annotations that apko
// sets for an image of n layers.
func imageConfig(ctx context.Context, ic types.ImageConfiguration, arch types.Architecture, created time.Time, n int) (*dockerspec.DockerOCIImage, map[string]string, error) {
	img, err := oci.BuildImageFromLayers(ctx, empty.Image, nil, ic, created, arch)
	if err != nil {
		return nil, nil, err
	}
	cfg, err := img.ConfigFile()
	if err != nil {
		return nil, nil, err
	}
	m, err := img.Manifest()
	if err != nil {
		return nil, nil, err
	}
	cfg = cfg.DeepCopy()
	comment := "This is an apko single-layer image"
	if n > 1 {
		comment = ""
	}
	title, hasTitle := ic.Annotations["org.opencontainers.image.title"]
	vendor, hasVendor := ic.Annotations["org.opencontainers.image.vendor"]
	if hasTitle && hasVendor {
		comment = title + " by " + vendor
	}
	cfg.History = nil
	for range n {
		cfg.History = append(cfg.History, v1.History{
			Created:   v1.Time{Time: created},
			CreatedBy: "apko",
			Author:    "apko",
			Comment:   comment,
		})
	}
	// dockerui takes the config as BuildKit's type. Both types encode the
	// same OCI image config JSON.
	data, err := json.Marshal(cfg)
	if err != nil {
		return nil, nil, err
	}
	var out dockerspec.DockerOCIImage
	if err := json.Unmarshal(data, &out); err != nil {
		return nil, nil, err
	}
	return &out, m.Annotations, nil
}

// specPlatform converts p to the image-spec type that BuildKit's API takes.
func specPlatform(p v1.Platform) ocispecs.Platform {
	return ocispecs.Platform{
		OS:           p.OS,
		Architecture: p.Architecture,
		Variant:      p.Variant,
		OSVersion:    p.OSVersion,
		OSFeatures:   p.OSFeatures,
	}
}

// ggcrPlatform converts a platform from BuildKit's API.
func ggcrPlatform(p ocispecs.Platform) v1.Platform {
	return v1.Platform{
		OS:           p.OS,
		Architecture: p.Architecture,
		Variant:      p.Variant,
		OSVersion:    p.OSVersion,
		OSFeatures:   p.OSFeatures,
	}
}

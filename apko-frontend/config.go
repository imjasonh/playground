package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"slices"
	"strings"

	"chainguard.dev/apko/pkg/apk/apk"
	"chainguard.dev/apko/pkg/build"
	"chainguard.dev/apko/pkg/build/types"
	"chainguard.dev/apko/pkg/lock"
	"chainguard.dev/apko/pkg/tarfs"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"gopkg.in/yaml.v3"
)

// parseConfig decodes an apko configuration the way apko does, rejecting
// unknown fields, and refuses the features this frontend doesn't support.
func parseConfig(data []byte) (types.ImageConfiguration, error) {
	var ic types.ImageConfiguration
	dec := yaml.NewDecoder(bytes.NewReader(data))
	dec.KnownFields(true)
	if err := dec.Decode(&ic); errors.Is(err, io.EOF) {
		return ic, errors.New("the apko configuration is empty")
	} else if err != nil {
		return ic, fmt.Errorf("parsing apko configuration: %w", err)
	}
	if ic.Include != "" {
		return ic, errors.New("include is not supported; inline the included configuration")
	}
	if ic.Contents.BaseImage != nil {
		return ic, errors.New("contents.baseimage is not supported")
	}
	if f := ic.Format.Resolved(); f != types.LayerFormatTar {
		return ic, fmt.Errorf("format %q is not supported; BuildKit layers are tar layers", f)
	}
	ic.Contents.BuildRepositories = trimRepos(ic.Contents.BuildRepositories)
	ic.Contents.RuntimeOnlyRepositories = trimRepos(ic.Contents.RuntimeOnlyRepositories)
	ic.Contents.Repositories = trimRepos(ic.Contents.Repositories)
	return ic, nil
}

func trimRepos(repos []string) []string {
	out := make([]string, 0, len(repos))
	for _, r := range repos {
		out = append(out, strings.TrimRight(r, "/"))
	}
	return out
}

// configPlatforms returns the platforms that the configuration's archs list
// names, or nil when it names none.
func configPlatforms(ic types.ImageConfiguration) []v1.Platform {
	archs := ic.Archs
	if slices.Contains(archs, types.Architecture("all")) {
		archs = types.AllArchs
	}
	var out []v1.Platform
	seen := map[types.Architecture]bool{}
	for _, a := range archs {
		a = types.ParseArchitecture(a.String())
		if seen[a] {
			continue
		}
		seen[a] = true
		out = append(out, *a.ToOCIPlatform())
	}
	return out
}

// platformArch returns the apko architecture for an OCI platform.
func platformArch(p v1.Platform) types.Architecture {
	if p.Architecture == "arm" {
		v := p.Variant
		if v == "" {
			v = "v7"
		}
		return types.ParseArchitecture("arm/" + v)
	}
	return types.ParseArchitecture(p.Architecture)
}

// newBuildContext returns an apko build context for arch whose HTTP requests
// go through t. Creating it fetches the keyring and initializes the apk
// database, as apko does.
func newBuildContext(ctx context.Context, ic types.ImageConfiguration, arch types.Architecture, t http.RoundTripper, opts ...build.Option) (*build.Context, error) {
	return build.New(ctx, tarfs.New(), append([]build.Option{
		build.WithImageConfiguration(ic),
		build.WithArch(arch),
		build.WithoutDiskCache(),
		build.WithTransport(t),
	}, opts...)...)
}

// locked is one architecture's configuration with its packages pinned, and
// the lock the helper installs them from. The helper never resolves
// packages, so it needs no indexes, and an index that changes without
// changing the resolved packages doesn't invalidate the helper's cached
// result.
type locked struct {
	ic       types.ImageConfiguration
	pkgs     []lock.LockPkg
	lockData []byte
}

// resolve resolves the configuration's packages for every arch at once, as
// apko build does, so that each package has the same version on every
// arch. It fetches indexes and keys through t, and apko verifies each
// index's signature with the keyring. Each arch's configuration lists every
// installed package pinned to its version.
func resolve(ctx context.Context, ic types.ImageConfiguration, archs []types.Architecture, t http.RoundTripper) (map[types.Architecture]*locked, error) {
	ic.Archs = archs
	ics, missing, _, err := build.LockImageConfigurationWithPackages(ctx, ic, build.WithoutDiskCache(), build.WithTransport(t))
	if err != nil {
		if len(missing) > 0 {
			return nil, fmt.Errorf("%w (missing packages: %v)", err, missing)
		}
		return nil, err
	}
	out := map[types.Architecture]*locked{}
	for _, arch := range archs {
		lic, ok := ics[arch.String()]
		if !ok {
			return nil, fmt.Errorf("apko resolved no configuration for %s", arch)
		}
		// apko build resolves the pinned configuration again and installs
		// packages in that order, which is the order of the installed
		// database. Resolving it here and locking that order gives the
		// helper the same database without the indexes.
		bc, err := newBuildContext(ctx, *lic, arch, t)
		if err != nil {
			return nil, err
		}
		// The second result lists packages that must not be installed
		// alongside these. apko build fails only if one is already
		// installed, which can't happen in an empty filesystem.
		pkgs, _, err := bc.BuildPackageList(ctx)
		if err != nil {
			return nil, err
		}
		l := lock.Lock{Version: "v1"}
		for _, p := range pkgs {
			l.Contents.Packages = append(l.Contents.Packages, lock.LockPkg{
				Name:    p.Name,
				URL:     p.URL(),
				Version: p.Version,
				// Use the image's arch rather than the package's, which is
				// "noarch" for some Alpine packages. apko installs only the
				// locked packages whose architecture matches the image.
				Architecture: arch.ToAPK(),
				Checksum:     p.ChecksumString(),
			})
		}
		data, err := json.Marshal(l)
		if err != nil {
			return nil, err
		}
		out[arch] = &locked{ic: *lic, pkgs: l.Contents.Packages, lockData: data}
	}
	return out, nil
}

// fromLock pins each arch's packages to the versions in a lock file, as apko
// build --lockfile does. apko installs locked packages without reading an
// index, and checks each package against the lock's checksum only. To keep
// every package tied to a signature, fromLock also fetches each arch's
// indexes through t, which verifies their signatures with the keyring, and
// requires every locked package to appear in one with the same version and
// checksum.
func fromLock(ctx context.Context, ic types.ImageConfiguration, archs []types.Architecture, l lock.Lock, data []byte, t http.RoundTripper) (map[types.Architecture]*locked, error) {
	pinned := l.Arch2LockedPackages(archs)
	out := map[types.Architecture]*locked{}
	for _, arch := range archs {
		pkgs, err := lockedPackages(l, arch)
		if err != nil {
			return nil, err
		}
		lic, err := deepCopy(ic)
		if err != nil {
			return nil, err
		}
		lic.Contents.Packages = pinned[arch.String()]
		lic.Archs = []types.Architecture{arch}
		bc, err := newBuildContext(ctx, lic, arch, t)
		if err != nil {
			return nil, err
		}
		indexes, err := bc.APK().GetRepositoryIndexes(ctx, false)
		if err != nil {
			return nil, err
		}
		if err := checkLocked(pkgs, indexes); err != nil {
			return nil, fmt.Errorf("%s: %w", arch, err)
		}
		out[arch] = &locked{ic: lic, pkgs: pkgs, lockData: data}
	}
	return out, nil
}

// checkLocked reports an error unless every locked package appears in one of
// the signed indexes with the same name, version, and checksum.
func checkLocked(pkgs []lock.LockPkg, indexes []apk.NamedIndex) error {
	signed := map[[3]string]bool{}
	for _, idx := range indexes {
		for _, p := range idx.Packages() {
			signed[[3]string{p.Name, p.Version, p.ChecksumString()}] = true
		}
	}
	var unsigned []string
	for _, p := range pkgs {
		if !signed[[3]string{p.Name, p.Version, p.Checksum}] {
			unsigned = append(unsigned, p.Name+"="+p.Version)
		}
	}
	if len(unsigned) > 0 {
		return fmt.Errorf("no signed repository index lists these locked packages with the locked checksum: %s", strings.Join(unsigned, ", "))
	}
	return nil
}

// lockedPackages returns the packages in l that apko installs for arch.
func lockedPackages(l lock.Lock, arch types.Architecture) ([]lock.LockPkg, error) {
	var out []lock.LockPkg
	for _, p := range l.Contents.Packages {
		if p.Architecture != arch.ToAPK() {
			continue
		}
		if p.Checksum == "" {
			return nil, fmt.Errorf("locked package %s has no checksum", p.Name)
		}
		out = append(out, p)
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("the lock has no packages for %s", arch.ToAPK())
	}
	return out, nil
}

func parseLock(data []byte) (lock.Lock, error) {
	var l lock.Lock
	if err := json.Unmarshal(data, &l); err != nil {
		return l, fmt.Errorf("parsing lock: %w", err)
	}
	return l, nil
}

func deepCopy(ic types.ImageConfiguration) (types.ImageConfiguration, error) {
	var out types.ImageConfiguration
	data, err := json.Marshal(ic)
	if err != nil {
		return out, err
	}
	err = json.Unmarshal(data, &out)
	return out, err
}

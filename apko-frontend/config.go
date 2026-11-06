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

	"chainguard.dev/apko/pkg/build"
	"chainguard.dev/apko/pkg/build/types"
	"chainguard.dev/apko/pkg/lock"
	"chainguard.dev/apko/pkg/tarfs"
	ocispecs "github.com/opencontainers/image-spec/specs-go/v1"
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
func configPlatforms(ic types.ImageConfiguration) []ocispecs.Platform {
	archs := ic.Archs
	if slices.Contains(archs, types.Architecture("all")) {
		archs = types.AllArchs
	}
	var out []ocispecs.Platform
	seen := map[types.Architecture]bool{}
	for _, a := range archs {
		a = types.ParseArchitecture(a.String())
		if seen[a] {
			continue
		}
		seen[a] = true
		p := a.ToOCIPlatform()
		out = append(out, ocispecs.Platform{OS: p.OS, Architecture: p.Architecture, Variant: p.Variant})
	}
	return out
}

// platformArch returns the apko architecture for an OCI platform.
func platformArch(p ocispecs.Platform) types.Architecture {
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
// the packages to fetch for it.
type locked struct {
	ic   types.ImageConfiguration
	pkgs []lock.LockPkg
	// lockData is the user's lock file, which the helper installs from.
	// It is nil when the frontend resolved the packages, and the helper
	// resolves the pinned configuration again, as apko build does.
	lockData []byte
}

// resolve resolves the configuration's packages for every arch at once, as
// apko build does, so that each package has the same version on every
// arch. It fetches indexes and keys through t. Each arch's configuration
// lists every installed package pinned to its version.
func resolve(ctx context.Context, ic types.ImageConfiguration, archs []types.Architecture, t http.RoundTripper) (map[types.Architecture]*locked, error) {
	ic.Archs = archs
	ics, missing, resolved, err := build.LockImageConfigurationWithPackages(ctx, ic, build.WithoutDiskCache(), build.WithTransport(t))
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
		lk := &locked{ic: *lic}
		for _, p := range resolved[arch] {
			lk.pkgs = append(lk.pkgs, lock.LockPkg{
				Name:         p.Name,
				URL:          p.URL(),
				Version:      p.Version,
				Architecture: arch.ToAPK(),
				Checksum:     p.ChecksumString(),
			})
		}
		out[arch] = lk
	}
	return out, nil
}

// fromLock pins each arch's packages to the versions in a lock file, as apko
// build --lockfile does. It creates a build context for each arch through t,
// which fetches the keyring that the helper needs too.
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
		if _, err := newBuildContext(ctx, lic, arch, t); err != nil {
			return nil, err
		}
		out[arch] = &locked{ic: lic, lockData: data, pkgs: pkgs}
	}
	return out, nil
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

package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"path"
	"path/filepath"
	"slices"
	"strings"

	"chainguard.dev/apko/pkg/build/types"
)

// contextDir is where apko finds the build context's keyring files and
// local repositories, in the frontend and in the helper. apko resolves
// relative paths against its working directory, and records local package
// paths as absolute paths, so both processes run in this directory and
// see the same files at the same paths.
const contextDir = "/apko/context"

// localRepos returns the configuration's repositories that are directories
// rather than URLs. An entry may carry an "@tag " prefix.
func localRepos(ic types.ImageConfiguration) []string {
	var out []string
	for _, r := range slices.Concat(ic.Contents.BuildRepositories, ic.Contents.Repositories) {
		if _, u, tagged := strings.Cut(r, " "); tagged {
			r = u
		}
		if !isRemote(r) {
			out = append(out, r)
		}
	}
	return out
}

// localInputs returns the build-context paths apko reads while resolving
// packages for archs: keyring files, and the index of each local repository
// for each arch.
func localInputs(ic types.ImageConfiguration, archs []types.Architecture) ([]string, error) {
	var raw []string
	for _, k := range ic.Contents.Keyring {
		if !isRemote(k) {
			raw = append(raw, k)
		}
	}
	for _, r := range localRepos(ic) {
		for _, a := range archs {
			raw = append(raw, path.Join(r, a.ToAPK(), "APKINDEX.tar.gz"))
		}
	}
	out := make([]string, 0, len(raw))
	for _, p := range raw {
		cp, err := contextPath(p)
		if err != nil {
			return nil, err
		}
		out = append(out, cp)
	}
	slices.Sort(out)
	return slices.Compact(out), nil
}

// contextPath returns p relative to the root of the build context. p is
// relative to the context, a file:// URL, or an absolute path under
// contextDir, which is how apko records a local package's URL.
func contextPath(p string) (string, error) {
	p = strings.TrimPrefix(p, "file://")
	if filepath.IsAbs(p) {
		rel, err := filepath.Rel(contextDir, p)
		if err != nil || rel == ".." || strings.HasPrefix(rel, "../") {
			return "", fmt.Errorf("%s is outside the build context; use a path relative to the context", p)
		}
		p = rel
	}
	p = path.Clean(p)
	if p == ".." || strings.HasPrefix(p, "../") {
		return "", fmt.Errorf("%s is outside the build context", p)
	}
	return p, nil
}

// stage copies the given build-context files into contextDir and makes it
// the working directory, so that apko reads them as it would from a local
// checkout. A missing file is skipped, so apko reports it.
func (b *builder) stage(ctx context.Context, paths []string) error {
	if err := os.MkdirAll(contextDir, 0o755); err != nil {
		return err
	}
	for _, p := range paths {
		e, err := b.fetcher.entry(ctx, contextURL(p))
		if err != nil {
			return err
		}
		data, err := b.fetcher.get(ctx, e)
		if errors.Is(err, errNotFound) {
			continue
		} else if err != nil {
			return fmt.Errorf("reading %s from the build context: %w", p, err)
		}
		dst := filepath.Join(contextDir, filepath.FromSlash(p))
		if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(dst, data, 0o644); err != nil {
			return err
		}
	}
	return os.Chdir(contextDir)
}

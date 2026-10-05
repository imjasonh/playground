package kube

import (
	"context"
	"errors"
	"fmt"
	"path/filepath"
	"strings"
)

// Volume returns a Controller that declares a persistent volume at dir, for
// a program that keeps state on disk across restarts, such as a copy of
// each repository that it serves. Volume does nothing at run time. The
// generate command adds a PersistentVolumeClaim to the installation and
// mounts it at dir.
//
// A program with a volume runs one replica, so one Pod at a time writes the
// volume. Its Deployment replaces the Pod with the Recreate strategy: the old
// Pod stops before the new one starts. The program needs no leader election,
// and reconciles and its kube.Serve handler can share what's on disk.
//
// dir must be an absolute path, other than /, /app, and /tmp, which the
// root file system, the program, and temporary files use. It can't be
// /var/run/secrets/kubernetes.io/serviceaccount or /var/run/secrets/tokens,
// where the Pod's tokens are mounted, or a directory inside or above them.
// In many images, /var/run is a symbolic link to /run, so the same rule
// applies to /run/secrets/kubernetes.io/serviceaccount and
// /run/secrets/tokens. To run the program outside a cluster, give it a flag
// for the directory that defaults to dir.
//
// A program can have one Volume.
func Volume(dir string) Controller { return &volume{dir: dir} }

type volume struct{ dir string }

func (v *volume) check() error {
	switch {
	case !filepath.IsAbs(v.dir) || filepath.Clean(v.dir) != v.dir:
		return fmt.Errorf("kube.Volume: %q isn't a clean absolute path, such as /var/lib/program", v.dir)
	case v.dir == "/" || v.dir == "/app" || v.dir == "/tmp":
		return fmt.Errorf("kube.Volume: the installation uses %s for something else; use a directory such as /var/lib/program", v.dir)
	}
	// A volume at the service account's directory stops Kubernetes from
	// mounting the token there, and one at the token directory fails to
	// install. A volume inside either would be inside a read-only volume,
	// and one above them would hold their mount points.
	for _, tokens := range []string{serviceAccountDir, tokenDir} {
		// In chainguard/static and many other images, /var/run is a
		// symbolic link to /run, so the tokens are also under /run, where
		// their read-only volume hides a volume at the same directory.
		for _, dir := range []string{tokens, strings.TrimPrefix(tokens, "/var")} {
			if within(v.dir, dir) || within(dir, v.dir) {
				return fmt.Errorf("kube.Volume: %s overlaps %s, where the Pod's tokens are mounted; use a directory such as /var/lib/program", v.dir, dir)
			}
		}
	}
	return nil
}

// within reports whether path is dir or a path inside it. Both paths are
// clean.
func within(path, dir string) bool {
	return path == dir || strings.HasPrefix(path, dir+"/")
}

func (v *volume) prepare(_ context.Context, m *Manager) error {
	for _, c := range m.controllers {
		if o, ok := c.(*volume); ok && o != v {
			return errors.New("kube.Volume: the program declares more than one volume")
		}
	}
	return v.check()
}

func (v *volume) describe() (declared, error)         { return declared{volume: v.dir}, v.check() }
func (*volume) setup(context.Context, *Manager) error { return nil }
func (*volume) run(context.Context) error             { return nil }
func (*volume) reconciles() bool                      { return false }
func (*volume) controllerName() string                { return "volume" }
func (*volume) synced() bool                          { return true }

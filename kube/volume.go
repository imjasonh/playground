package kube

import (
	"context"
	"errors"
	"fmt"
	"path/filepath"
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
// root file system, the program, and temporary files use. To run the program
// outside a cluster, give it a flag for the directory that defaults to dir.
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
	return nil
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

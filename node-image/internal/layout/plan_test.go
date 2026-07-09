package layout_test

import (
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/fetch"
	"github.com/imjasonh/playground/node-image/internal/layer"
	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestPlanLayoutMatchesMaterializeStoreDiffID(t *testing.T) {
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}
	l, err := lock.ParseFile(filepath.Join(fixture, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	plat := resolve.Platform{OS: "linux", CPU: "x64", Libc: "glibc"}
	refs, err := resolve.Closure(l, ".", plat)
	if err != nil {
		t.Fatal(err)
	}
	direct := resolve.DirectDeps(l, ".")
	cacheDir := t.TempDir()
	cache := &fetch.Cache{Dir: cacheDir}
	tarballs := map[string]string{}
	keys := map[string]string{}
	for _, ref := range refs {
		path, err := cache.Ensure(ref.Tarball, ref.Integrity)
		if err != nil {
			t.Skipf("network/fetch unavailable: %v", err)
		}
		tarballs[ref.PackageID] = path
		key, err := fetch.IntegrityKey(ref.Integrity)
		if err != nil {
			t.Fatal(err)
		}
		keys[ref.PackageID] = key
	}

	stage := t.TempDir()
	if _, err := layout.Materialize(stage, l, refs, tarballs, direct); err != nil {
		t.Fatal(err)
	}
	diskPkgs, err := layer.StorePackagesFromDir(stage)
	if err != nil {
		t.Fatal(err)
	}

	spool := t.TempDir()
	planned, err := layout.PlanLayout(l, refs, tarballs, direct, layout.PlanOptions{
		SpoolRoot:    spool,
		IntegrityKey: keys,
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(planned.Store) != len(diskPkgs) {
		t.Fatalf("store packages: plan=%d disk=%d", len(planned.Store), len(diskPkgs))
	}
	for i := range diskPkgs {
		if diskPkgs[i].DepPath != planned.Store[i].DepPath {
			t.Fatalf("depPath order: disk=%q plan=%q", diskPkgs[i].DepPath, planned.Store[i].DepPath)
		}
		d1, err := layer.DiffID(diskPkgs[i].Files)
		if err != nil {
			t.Fatal(err)
		}
		d2, err := layer.DiffID(planned.Store[i].Files)
		if err != nil {
			t.Fatal(err)
		}
		if d1 != d2 {
			t.Fatalf("package %s DiffID mismatch:\n  disk %s (%d files)\n  plan %s (%d files)",
				diskPkgs[i].DepPath, d1, len(diskPkgs[i].Files), d2, len(planned.Store[i].Files))
		}
	}
	if len(planned.Links) == 0 {
		t.Fatal("expected top-level link layer entries")
	}
}

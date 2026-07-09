package layer_test

import (
	"io/fs"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layer"
)

func TestBucketOnePerPackageWhenUnderBudget(t *testing.T) {
	pkgs := []layer.PackageStore{
		{Name: "b", DepPath: "b@1.0.0", Files: []layer.File{{Rel: "node_modules/.pnpm/b@1.0.0/x", Mode: 0o644, Body: []byte("b")}}},
		{Name: "a", DepPath: "a@1.0.0", Files: []layer.File{{Rel: "node_modules/.pnpm/a@1.0.0/x", Mode: 0o644, Body: []byte("a")}}},
	}
	got := layer.BucketStorePackages(pkgs, 10)
	if len(got) != 2 {
		t.Fatalf("got %d buckets", len(got))
	}
	// sorted by DepPath: a then b
	if got[0][0].Rel != "node_modules/.pnpm/a@1.0.0/x" {
		t.Fatalf("order: %+v", got[0])
	}
}

func TestBucketStableHashWhenOverBudget(t *testing.T) {
	var pkgs []layer.PackageStore
	for _, name := range []string{"alpha", "beta", "gamma", "delta", "epsilon"} {
		pkgs = append(pkgs, layer.PackageStore{
			Name:    name,
			DepPath: name + "@1.0.0",
			Files:   []layer.File{{Rel: "p/" + name, Mode: 0o644, Body: []byte(name)}},
		})
	}
	a := layer.BucketStorePackages(pkgs, 2)
	b := layer.BucketStorePackages(pkgs, 2)
	if len(a) != 2 || len(b) != 2 {
		t.Fatalf("len %d %d", len(a), len(b))
	}
	// Same assignment
	d1, _ := layer.DiffID(a[0])
	d2, _ := layer.DiffID(b[0])
	if d1 != d2 {
		t.Fatal("bucketing not stable")
	}
	// Adding a package only changes its bucket
	pkgs2 := append(append([]layer.PackageStore{}, pkgs...), layer.PackageStore{
		Name: "zeta", DepPath: "zeta@1.0.0", Files: []layer.File{{Rel: "p/zeta", Mode: 0o644, Body: []byte("z")}},
	})
	c := layer.BucketStorePackages(pkgs2, 2)
	changed := 0
	for i := 0; i < 2; i++ {
		da, _ := layer.DiffID(a[i])
		dc, _ := layer.DiffID(c[i])
		if da != dc {
			changed++
		}
	}
	if changed != 1 {
		t.Fatalf("expected exactly one bucket to change, got %d", changed)
	}
}

func TestBudgetStoreSlots(t *testing.T) {
	b := layer.Budget{MaxLayers: 127, BaseLayers: 10, ExtraLayers: 2}
	if b.StoreSlots() != 115 {
		t.Fatalf("slots=%d", b.StoreSlots())
	}
	b = layer.Budget{MaxLayers: 5, BaseLayers: 10, ExtraLayers: 2}
	if b.StoreSlots() != 1 {
		t.Fatalf("slots=%d", b.StoreSlots())
	}
	_ = fs.ModeDir
}

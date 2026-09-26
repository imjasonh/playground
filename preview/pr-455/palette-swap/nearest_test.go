package palette

import (
	"math/rand/v2"
	"testing"
)

func TestCatalogCounts(t *testing.T) {
	want := map[string]int{
		"grey":   16,
		"nes":    54,
		"perler": 103,
		"floss":  456,
	}
	if len(Catalog) != len(want) {
		t.Fatalf("catalog length %d, want %d", len(Catalog), len(want))
	}
	seen := map[string]bool{}
	for _, p := range Catalog {
		if seen[p.ID] {
			t.Fatalf("duplicate id %s", p.ID)
		}
		seen[p.ID] = true
		if len(p.Colors) != want[p.ID] {
			t.Fatalf("%s has %d colors, want %d", p.ID, len(p.Colors), want[p.ID])
		}
		if len(p.Colors) > MaxIndex() {
			t.Fatalf("%s does not fit in a uint16 index", p.ID)
		}
		for i, c := range p.Colors {
			if c.R < 0 || c.R > 255 || c.G < 0 || c.G > 255 || c.B < 0 || c.B > 255 {
				t.Fatalf("%s color %d %s is outside 0..255", p.ID, i, c.Name)
			}
		}
	}
}

func TestNearestKnown(t *testing.T) {
	pal := []Color{
		{R: 255, G: 0, B: 0},
		{R: 0, G: 255, B: 0},
		{R: 0, G: 0, B: 255},
	}
	// The first pixel is nearer red. The second is nearer blue.
	// The third is equidistant from red and green, so the earlier entry wins.
	// The fourth is black and equidistant from all three.
	r := []int32{250, 10, 128, 0}
	g := []int32{10, 10, 128, 0}
	b := []int32{10, 200, 0, 0}
	idx := make([]int32, len(r))
	NearestScalar(idx, r, g, b, pal)
	want := []int32{0, 2, 0, 0}
	for i := range want {
		if idx[i] != want[i] {
			t.Fatalf("pixel %d index %d, want %d", i, idx[i], want[i])
		}
	}
}

func TestNearestEmpty(t *testing.T) {
	idx := []int32{4, 5, 6}
	NearestScalar(idx, []int32{1, 2, 3}, []int32{1, 2, 3}, []int32{1, 2, 3}, nil)
	for i, v := range idx {
		if v != 0 {
			t.Fatalf("empty palette left index %d as %d", i, v)
		}
	}
	idx = []int32{9}
	NearestScalar(idx[:0], nil, nil, nil, Catalog[0].Colors)
	if idx[0] != 9 {
		t.Fatal("empty image changed the index buffer")
	}
}

func TestNearestLengthMismatch(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("mismatched planes did not panic")
		}
	}()
	NearestScalar([]int32{0}, []int32{0, 1}, []int32{0}, []int32{0}, Catalog[0].Colors)
}

func TestImplementationsAgree(t *testing.T) {
	if len(impls) == 0 {
		t.Fatal("no implementations registered")
	}
	rng := rand.New(rand.NewPCG(1, 2))
	const n = 1007
	r := make([]int32, n)
	g := make([]int32, n)
	b := make([]int32, n)
	for i := range r {
		r[i] = int32(rng.IntN(256))
		g[i] = int32(rng.IntN(256))
		b[i] = int32(rng.IntN(256))
	}
	for _, p := range Catalog {
		ref := make([]int32, n)
		NearestScalar(ref, r, g, b, p.Colors)
		for _, impl := range impls {
			got := make([]int32, n)
			impl.fn(got, r, g, b, p.Colors)
			for i := range ref {
				if got[i] != ref[i] {
					t.Fatalf("%s pixel %d on %s: got %d, scalar %d", impl.name, i, p.ID, got[i], ref[i])
				}
			}
		}
	}
}

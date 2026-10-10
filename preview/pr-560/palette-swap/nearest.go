package palette

import "math"

// Color is one palette entry. R, G, and B are sRGB channel values, normally 0 to 255.
type Color struct {
	Name    string
	R, G, B int32
}

// Palette is a named list of colors the page can select.
type Palette struct {
	ID     string
	Name   string
	Colors []Color
}

// Catalog is the palettes offered to the page, from fewest colors to most.
var Catalog = []Palette{
	{ID: "grey", Name: "Greyscale", Colors: greyColors},
	{ID: "nes", Name: "NES", Colors: nesColors},
	{ID: "perler", Name: "Perler beads", Colors: perlerColors},
	{ID: "floss", Name: "Embroidery floss", Colors: flossColors},
}

// Find returns the palette with the given id.
func Find(id string) (Palette, bool) {
	for _, p := range Catalog {
		if p.ID == id {
			return p, true
		}
	}
	return Palette{}, false
}

type nearestFn func(idx, r, g, b []int32, pal []Color)

type namedFn struct {
	name string
	fn   nearestFn
}

// impls is filled by init functions. The scalar mapper is always present.
// Portable and Wasm archsimd mappers register themselves when those files
// are included in the build.
var impls []namedFn

func register(name string, fn nearestFn) {
	impls = append(impls, namedFn{name: name, fn: fn})
}

func init() {
	register("scalar", NearestScalar)
}

// bestSentinel is larger than any squared distance of three byte channels.
// 255² × 3 is 195075.
const bestSentinel int32 = 1 << 30

func prepare(idx, r, g, b []int32, pal []Color) bool {
	n := len(r)
	if len(g) != n || len(b) != n || len(idx) != n {
		panic("palette: plane length mismatch")
	}
	if n == 0 || len(pal) == 0 {
		for i := range idx {
			idx[i] = 0
		}
		return false
	}
	return true
}

// NearestScalar writes, for each pixel, the index of the closest palette color.
// r, g, b, and idx must have the same length. Channel values are sRGB bytes
// stored as int32.
func NearestScalar(idx, r, g, b []int32, pal []Color) {
	if !prepare(idx, r, g, b, pal) {
		return
	}
	for i := range r {
		bestD := bestSentinel
		best := int32(0)
		ri, gi, bi := r[i], g[i], b[i]
		for k := range pal {
			dr := ri - pal[k].R
			dg := gi - pal[k].G
			db := bi - pal[k].B
			d := dr*dr + dg*dg + db*db
			if d < bestD {
				bestD = d
				best = int32(k)
			}
		}
		idx[i] = best
	}
}

// Checksum is the sum of palette indexes. Tests and the page use it to
// compare implementations.
func Checksum(idx []int32) uint64 {
	var s uint64
	for _, v := range idx {
		s += uint64(v)
	}
	return s
}

// MaxIndex is the largest palette index Checksum and the page encoding can hold.
func MaxIndex() int {
	return math.MaxUint16
}

//go:build goexperiment.simd

package palette

import "simd"

func init() {
	register("portable", NearestPortable)
}

// PortableLanes is the int32 lane count of the portable vector in this process.
// On Wasm that count is 4.
func PortableLanes() int {
	var v simd.Int32s
	return v.Len()
}

// PortableEmulated reports whether the portable API is running in software.
func PortableEmulated() bool {
	return simd.Emulated()
}

func nearestPortable(rv, gv, bv simd.Int32s, pal []Color) simd.Int32s {
	bestD := simd.BroadcastInt32s(bestSentinel)
	bestI := simd.BroadcastInt32s(0)
	for k := range pal {
		dr := rv.Sub(simd.BroadcastInt32s(pal[k].R))
		dg := gv.Sub(simd.BroadcastInt32s(pal[k].G))
		db := bv.Sub(simd.BroadcastInt32s(pal[k].B))
		dist := dr.Mul(dr).Add(dg.Mul(dg)).Add(db.Mul(db))
		closer := dist.Less(bestD)
		bestD = dist.IfElse(closer, bestD)
		bestI = simd.BroadcastInt32s(int32(k)).IfElse(closer, bestI)
	}
	return bestI
}

// NearestPortable is NearestScalar written with the platform-agnostic simd package.
// The chunk width comes from the vector's Len. A short tail uses a partial load.
func NearestPortable(idx, r, g, b []int32, pal []Color) {
	if !prepare(idx, r, g, b, pal) {
		return
	}
	n := len(r)
	width := PortableLanes()
	i := 0
	for ; i+width <= n; i += width {
		rv := simd.LoadInt32s(r[i : i+width])
		gv := simd.LoadInt32s(g[i : i+width])
		bv := simd.LoadInt32s(b[i : i+width])
		nearestPortable(rv, gv, bv, pal).Store(idx[i : i+width])
	}
	if i < n {
		rv, got := simd.LoadInt32sPart(r[i:])
		gv, _ := simd.LoadInt32sPart(g[i:])
		bv, _ := simd.LoadInt32sPart(b[i:])
		nearestPortable(rv, gv, bv, pal).StorePart(idx[i : i+got])
	}
}

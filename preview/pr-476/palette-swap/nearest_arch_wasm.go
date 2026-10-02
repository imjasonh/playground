//go:build goexperiment.simd && wasm

package palette

import "simd/archsimd"

func init() {
	register("arch", NearestArch)
}

func nearestArch(rv, gv, bv archsimd.Int32x4, pal []Color) archsimd.Int32x4 {
	bestD := archsimd.BroadcastInt32x4(bestSentinel)
	bestI := archsimd.BroadcastInt32x4(0)
	for k := range pal {
		dr := rv.Sub(archsimd.BroadcastInt32x4(pal[k].R))
		dg := gv.Sub(archsimd.BroadcastInt32x4(pal[k].G))
		db := bv.Sub(archsimd.BroadcastInt32x4(pal[k].B))
		dist := dr.Mul(dr).Add(dg.Mul(dg)).Add(db.Mul(db))
		closer := dist.Less(bestD)
		bestD = dist.IfElse(closer, bestD)
		bestI = archsimd.BroadcastInt32x4(int32(k)).IfElse(closer, bestI)
	}
	return bestI
}

// NearestArch is NearestScalar written with Wasm's fixed Int32x4 type.
// That type has no partial load in Go 1.27, so the tail calls NearestScalar.
func NearestArch(idx, r, g, b []int32, pal []Color) {
	if !prepare(idx, r, g, b, pal) {
		return
	}
	const width = 4
	n := len(r)
	i := 0
	for ; i+width <= n; i += width {
		rv := archsimd.LoadInt32x4(r[i : i+width])
		gv := archsimd.LoadInt32x4(g[i : i+width])
		bv := archsimd.LoadInt32x4(b[i : i+width])
		nearestArch(rv, gv, bv, pal).Store(idx[i : i+width])
	}
	if i < n {
		NearestScalar(idx[i:], r[i:], g[i:], b[i:], pal)
	}
}

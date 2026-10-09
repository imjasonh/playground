package sim

import (
	"math"
	"sync"
)

// The walls act as if liquid at rest filled the space beyond them. Without
// that, particles at a wall would see no neighbors on one side, read a low
// density, and pack into a dense, jittery layer against the wall.
//
// A particle at distance d from a wall sees virtual liquid filling the half
// plane beyond it, with the number density of the lattice that scenes are laid
// out on. Integrating the solver's kernels over that half plane, in polar
// coordinates around the particle, gives four functions of d:
//
//	density      2n ∫ (1-r)² · r·acos(d/r) dr
//	near density 2n ∫ (1-r)³ · r·acos(d/r) dr
//	push         2n ∫ (1-r)  · √(r²-d²) dr
//	near push    2n ∫ (1-r)² · √(r²-d²) dr
//
// with r running from d to 1. The density terms add to the particle's own
// density. The push terms are the components, normal to the wall, of the
// displacement the virtual neighbors apply, per unit of pressure.

const wallSamples = 64

type wallTable struct {
	rho, rhoNear, push, pushNear [wallSamples + 2]float64
}

var walls = sync.OnceValue(func() *wallTable {
	return newWallTable(Spacing)
})

func newWallTable(spacing float64) *wallTable {
	n := 1 / (spacing * spacing * math.Sqrt(3) / 2)
	t := new(wallTable)
	const steps = 512
	for s := 0; s <= wallSamples; s++ {
		d := float64(s) / wallSamples
		dr := (1 - d) / steps
		var rho, rhoNear, push, pushNear float64
		for k := range steps {
			r := d + (float64(k)+0.5)*dr
			c := 1 - r
			arc := r * math.Acos(d/r)
			normal := math.Sqrt(r*r - d*d)
			rho += c * c * arc
			rhoNear += c * c * c * arc
			push += c * normal
			pushNear += c * c * normal
		}
		t.rho[s] = 2 * n * rho * dr
		t.rhoNear[s] = 2 * n * rhoNear * dr
		t.push[s] = 2 * n * push * dr
		t.pushNear[s] = 2 * n * pushNear * dr
	}
	return t
}

// at returns the wall terms for a particle at distance d from a wall, where
// 0 <= d < 1.
func (t *wallTable) at(d float64) (rho, rhoNear, push, pushNear float64) {
	f := max(d, 0) * wallSamples
	i := int(f)
	if i >= wallSamples {
		return 0, 0, 0, 0
	}
	a := f - float64(i)
	lerp := func(v *[wallSamples + 2]float64) float64 { return v[i] + (v[i+1]-v[i])*a }
	return lerp(&t.rho), lerp(&t.rhoNear), lerp(&t.push), lerp(&t.pushNear)
}

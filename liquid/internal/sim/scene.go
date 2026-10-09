package sim

import "math"

// Scene is a starting arrangement of liquid.
type Scene int

// Scenes, in the order the interface lists them.
const (
	SceneDam Scene = iota
	SceneDouble
	SceneDrop
	ScenePool
	SceneBlob
)

// Scenes lists every scene.
var Scenes = []Scene{SceneDam, SceneDouble, SceneDrop, ScenePool, SceneBlob}

// String returns the scene's display name.
func (s Scene) String() string {
	switch s {
	case SceneDam:
		return "dam break"
	case SceneDouble:
		return "double dam"
	case SceneDrop:
		return "droplet"
	case ScenePool:
		return "pool"
	case SceneBlob:
		return "zero-g blob"
	default:
		return "unknown"
	}
}

// Short returns a one-word name for compact labels.
func (s Scene) Short() string {
	switch s {
	case SceneDam:
		return "dam"
	case SceneDouble:
		return "double"
	case SceneDrop:
		return "drop"
	case ScenePool:
		return "pool"
	case SceneBlob:
		return "blob"
	default:
		return "?"
	}
}

// Fill returns the fraction of the tank's area that the scene fills with
// liquid. Callers use it to pick a scale that yields a target particle count.
func (s Scene) Fill() float64 {
	switch s {
	case SceneDam:
		return 0.42 * 0.8
	case SceneDouble:
		return 2 * 0.26 * 0.7
	case SceneDrop:
		return 0.3 + math.Pi*0.13*0.13*0.9
	case ScenePool:
		return 0.45
	case SceneBlob:
		return 0.24
	default:
		return 0.3
	}
}

// Gravity returns the gravity direction the scene starts with.
func (s Scene) Gravity() Vec {
	if s == SceneBlob {
		return Vec{}
	}
	return Vec{0, 1}
}

// Populate clears the tank, sets the scene's gravity, and fills the tank with
// the scene's liquid. Particles get a dye of 0 or 1 so that two-tone themes
// show how the liquid mixes.
func (w *World) Populate(s Scene) {
	w.Clear()
	w.Gravity = s.Gravity()
	W, H := w.Width, w.Height
	switch s {
	case SceneDam:
		w.fillRect(0, H*0.2, W*0.42, H, func(x, _ float64) float32 {
			return dyeIf(x > W*0.21)
		})
	case SceneDouble:
		w.fillRect(0, H*0.3, W*0.26, H, func(float64, float64) float32 { return 0 })
		w.fillRect(W*0.74, H*0.3, W, H, func(float64, float64) float32 { return 1 })
	case SceneDrop:
		w.fillRect(0, H*0.7, W, H, func(float64, float64) float32 { return 0 })
		r := 0.13 * math.Sqrt(W*H)
		w.fillDisc(W*0.5, math.Max(H*0.25, r+Spacing), r, func(float64, float64) float32 { return 1 })
	case ScenePool:
		w.fillRect(0, H*0.55, W, H, func(x, _ float64) float32 {
			return dyeIf(x > W*0.5)
		})
	case SceneBlob:
		r := math.Sqrt(0.24 * W * H / math.Pi)
		r = math.Min(r, 0.45*math.Min(W, H))
		w.fillDisc(W*0.5, H*0.5, r, func(x, _ float64) float32 {
			return dyeIf(x > W*0.5)
		})
	}
	w.nbrValid = false
}

func dyeIf(b bool) float32 {
	if b {
		return 1
	}
	return 0
}

// fillRect fills the rectangle [x0, x1] × [y0, y1] with particles on a
// triangular lattice, starting from the bottom so the rows sit on the floor.
func (w *World) fillRect(x0, y0, x1, y1 float64, dye func(x, y float64) float32) {
	w.fill(func(x, y float64) bool {
		return x >= x0 && x <= x1 && y >= y0 && y <= y1
	}, dye)
}

// fillDisc fills a disc centered on (cx, cy) with particles.
func (w *World) fillDisc(cx, cy, r float64, dye func(x, y float64) float32) {
	w.fill(func(x, y float64) bool {
		dx, dy := x-cx, y-cy
		return dx*dx+dy*dy <= r*r
	}, dye)
}

func (w *World) fill(inside func(x, y float64) bool, dye func(x, y float64) float32) {
	rowHeight := Spacing * math.Sqrt(3) / 2
	jitter := Spacing * 0.05
	for row := 0; ; row++ {
		y := w.Height - Spacing/2 - float64(row)*rowHeight
		if y < 0 {
			return
		}
		offset := Spacing / 2
		if row%2 != 0 {
			offset = Spacing
		}
		for x := offset; x < w.Width; x += Spacing {
			if !inside(x, y) {
				continue
			}
			jx := (w.rng.Float64() - 0.5) * jitter
			jy := (w.rng.Float64() - 0.5) * jitter
			w.Add(x+jx, y+jy, 0, 0, dye(x, y))
		}
	}
}

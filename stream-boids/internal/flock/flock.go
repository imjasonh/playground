// Package flock simulates boids on a torus.
//
// Each step sorts the boids into a uniform grid whose cells are one
// neighbor radius wide, copies their state into that order, and updates
// every boid from the copy. Workers read only the copy and write only their
// own boids, so a step needs no locks. A Flock is not safe for concurrent
// use.
package flock

import (
	"math"

	"github.com/imjasonh/playground/stream-boids/internal/par"
)

// Params tunes the flock. Distances are in pixels and speeds in pixels per
// second.
type Params struct {
	// Neighbors is how many neighbors a boid would have if the flock were
	// spread evenly. The neighbor radius shrinks as the flock grows so that
	// this stays about the same.
	Neighbors float64
	// MinRadius and MaxRadius bound the neighbor radius.
	MinRadius, MaxRadius float32
	// MaxNeighbors caps how many neighbors one boid reads, which bounds the
	// cost of a dense clump.
	MaxNeighbors int

	Separation, Alignment, Cohesion, Wander float32
	MinSpeed, MaxSpeed                      float32

	// Flow steers boids along a slowly turning field of swirls, so the flock
	// breaks into streams instead of settling on one heading. FlowSpeed is
	// how fast the swirls turn, in radians per second.
	Flow, FlowSpeed float32
}

// DefaultParams returns parameters that keep a flock of a few thousand
// boids from collapsing into one clump at 1080p.
func DefaultParams() Params {
	return Params{
		Neighbors:    18,
		MinRadius:    14,
		MaxRadius:    140,
		MaxNeighbors: 20,
		Separation:   2600,
		Alignment:    2.2,
		Cohesion:     0.9,
		Wander:       90,
		MinSpeed:     70,
		MaxSpeed:     230,
		Flow:         2,
		FlowSpeed:    0.15,
	}
}

type impulse struct {
	x, y, radius, strength float32
}

// wave is one term of the flow field's stream function,
// amp * sin(kx*x + ky*y + omega*t + phase). Each wave number is a whole
// number of periods across the world, so the field wraps seamlessly.
type wave struct {
	kx, ky, omega, phase, amp float32
}

// flowCell is the spacing of the grid the flow field is sampled on, in
// pixels.
const flowCell = 48

// Flock is a set of boids in a Width by Height world that wraps at the
// edges.
type Flock struct {
	Width, Height float32
	params        Params
	workers       int

	// Boid state, indexed by boid. Indices are stable across steps; Resize
	// removes boids from the end.
	X, Y, VX, VY []float32
	rng          []uint32
	seed         uint32

	// Neighbor grid, rebuilt each step.
	radius     float32
	gw, gh     int
	cellOf     []int32
	cellStart  []int32
	order      []int32
	sx, sy     []float32
	svx, svy   []float32
	impulses   []impulse
	pendingImp []impulse

	// Flow field, sampled at the corners of flowCell squares each step.
	t            float32
	waves        []wave
	fw, fh       int
	flowX, flowY []float32
}

// New returns an empty flock. workers is how many goroutines a step uses.
func New(width, height float32, params Params, workers int, seed uint32) *Flock {
	if seed == 0 {
		seed = 1
	}
	f := &Flock{Width: width, Height: height, params: params, workers: max(workers, 1), seed: seed}
	f.fw = int(width/flowCell) + 2
	f.fh = int(height/flowCell) + 2
	f.flowX = make([]float32, f.fw*f.fh)
	f.flowY = make([]float32, f.fw*f.fh)
	var norm float32
	for range 4 {
		s := f.nextSeed()
		m := float32(1 + int(unit(&s)*3))
		n := float32(1 + int(unit(&s)*2))
		if unit(&s) < 0.5 {
			n = -n
		}
		w := wave{
			kx:    2 * math.Pi * m / width,
			ky:    2 * math.Pi * n / height,
			omega: params.FlowSpeed * (0.5 + unit(&s)),
			phase: unit(&s) * 2 * math.Pi,
			amp:   0.5 + unit(&s),
		}
		if unit(&s) < 0.5 {
			w.omega = -w.omega
		}
		f.waves = append(f.waves, w)
		norm += w.amp * float32(math.Hypot(float64(w.kx), float64(w.ky)))
	}
	// Scale so the field's speed never exceeds 1.
	for i := range f.waves {
		f.waves[i].amp /= norm
	}
	return f
}

// Len returns the number of boids.
func (f *Flock) Len() int { return len(f.X) }

// Radius returns the neighbor radius for the current flock size.
func (f *Flock) Radius() float32 { return f.radius }

// Resize grows the flock to n boids, adding them at random positions with
// random headings, or shrinks it by dropping boids from the end.
func (f *Flock) Resize(n int) {
	n = max(n, 0)
	old := len(f.X)
	if n < old {
		f.X, f.Y, f.VX, f.VY, f.rng = f.X[:n], f.Y[:n], f.VX[:n], f.VY[:n], f.rng[:n]
	}
	for i := old; i < n; i++ {
		s := f.nextSeed()
		x := unit(&s) * f.Width
		y := unit(&s) * f.Height
		a := unit(&s) * 2 * math.Pi
		sp := f.params.MinSpeed + unit(&s)*(f.params.MaxSpeed-f.params.MinSpeed)
		f.X = append(f.X, x)
		f.Y = append(f.Y, y)
		f.VX = append(f.VX, sp*float32(math.Cos(float64(a))))
		f.VY = append(f.VY, sp*float32(math.Sin(float64(a))))
		f.rng = append(f.rng, s)
	}
	f.layout()
}

// Kick pushes boids within radius of (x, y) away from it on the next step.
// strength is the speed added at the center, in pixels per second.
func (f *Flock) Kick(x, y, radius, strength float32) {
	f.pendingImp = append(f.pendingImp, impulse{x, y, radius, strength})
}

// Swap exchanges boids i and j.
func (f *Flock) Swap(i, j int) {
	f.X[i], f.X[j] = f.X[j], f.X[i]
	f.Y[i], f.Y[j] = f.Y[j], f.Y[i]
	f.VX[i], f.VX[j] = f.VX[j], f.VX[i]
	f.VY[i], f.VY[j] = f.VY[j], f.VY[i]
	f.rng[i], f.rng[j] = f.rng[j], f.rng[i]
}

func (f *Flock) nextSeed() uint32 {
	f.seed = xorshift(f.seed)
	return f.seed
}

// layout sizes the grid for the current flock size.
func (f *Flock) layout() {
	n := max(len(f.X), 1)
	r := float32(math.Sqrt(f.params.Neighbors * float64(f.Width) * float64(f.Height) / (math.Pi * float64(n))))
	r = min(max(r, f.params.MinRadius), f.params.MaxRadius)
	// At least three cells across, so the 3x3 neighborhood never visits a
	// cell twice.
	gw := max(int(f.Width/r), 3)
	gh := max(int(f.Height/r), 3)
	f.radius = r
	f.gw, f.gh = gw, gh
	f.cellStart = grow(f.cellStart, gw*gh+1)
}

func (f *Flock) cell(x, y float32) int32 {
	cx := min(int(x*float32(f.gw)/f.Width), f.gw-1)
	cy := min(int(y*float32(f.gh)/f.Height), f.gh-1)
	return int32(cy*f.gw + cx)
}

// Step advances the flock by dt seconds.
func (f *Flock) Step(dt float32) {
	n := len(f.X)
	f.impulses, f.pendingImp = f.pendingImp, f.impulses[:0]
	if n == 0 {
		f.impulses = f.impulses[:0]
		return
	}
	f.sort()
	f.sampleFlow()

	par.For(n, f.workers, func(lo, hi int) {
		for k := lo; k < hi; k++ {
			f.update(k, dt)
		}
	})
	f.impulses = f.impulses[:0]
	f.t += dt
}

// sampleFlow evaluates the flow field at the grid corners. The field is the
// curl of a sum of waves, so it has no sources or sinks for boids to pile
// into.
func (f *Flock) sampleFlow() {
	for gy := range f.fh {
		y := float32(gy * flowCell)
		for gx := range f.fw {
			x := float32(gx * flowCell)
			var vx, vy float32
			for _, w := range f.waves {
				c := w.amp * float32(math.Cos(float64(w.kx*x+w.ky*y+w.omega*f.t+w.phase)))
				vx += w.ky * c
				vy -= w.kx * c
			}
			f.flowX[gy*f.fw+gx] = vx
			f.flowY[gy*f.fw+gx] = vy
		}
	}
}

// flow returns the field at (x, y), interpolated between grid corners.
func (f *Flock) flow(x, y float32) (float32, float32) {
	gx, gy := x/flowCell, y/flowCell
	ix, iy := min(int(gx), f.fw-2), min(int(gy), f.fh-2)
	tx, ty := gx-float32(ix), gy-float32(iy)
	i := iy*f.fw + ix
	lerp := func(s []float32) float32 {
		top := s[i] + (s[i+1]-s[i])*tx
		bot := s[i+f.fw] + (s[i+f.fw+1]-s[i+f.fw])*tx
		return top + (bot-top)*ty
	}
	return lerp(f.flowX), lerp(f.flowY)
}

// sort counts boids per cell and copies their state into cell order.
func (f *Flock) sort() {
	n := len(f.X)
	f.cellOf = grow(f.cellOf, n)
	f.order = grow(f.order, n)
	f.sx, f.sy = grow(f.sx, n), grow(f.sy, n)
	f.svx, f.svy = grow(f.svx, n), grow(f.svy, n)
	clear(f.cellStart)
	for i := range n {
		c := f.cell(f.X[i], f.Y[i])
		f.cellOf[i] = c
		f.cellStart[c+1]++
	}
	for c := 1; c < len(f.cellStart); c++ {
		f.cellStart[c] += f.cellStart[c-1]
	}
	// cellStart[c] now marks the start of cell c. Fill each cell from the
	// back so the counters end at the starts again.
	for i := n - 1; i >= 0; i-- {
		c := f.cellOf[i]
		f.cellStart[c+1]--
		k := f.cellStart[c+1]
		f.order[k] = int32(i)
	}
	// The loop above moved every end marker back to its cell's start, so
	// shift by one cell to restore cellStart[c] as the start of cell c.
	copy(f.cellStart[:len(f.cellStart)-1], f.cellStart[1:])
	f.cellStart[len(f.cellStart)-1] = int32(n)
	par.For(n, f.workers, func(lo, hi int) {
		for k := lo; k < hi; k++ {
			i := f.order[k]
			f.sx[k], f.sy[k], f.svx[k], f.svy[k] = f.X[i], f.Y[i], f.VX[i], f.VY[i]
		}
	})
}

// update computes the next state of the boid at sorted index k and writes
// it to that boid's own index.
func (f *Flock) update(k int, dt float32) {
	p := &f.params
	i := f.order[k]
	x, y, vx, vy := f.sx[k], f.sy[k], f.svx[k], f.svy[k]
	w, h := f.Width, f.Height
	hw, hh := w/2, h/2
	r2 := f.radius * f.radius
	sep := f.radius * 0.45
	sep2 := sep * sep

	var count int
	var avx, avy, cx, cy, fx, fy float32
	cell := int(f.cellOf[i])
	gx, gy := cell%f.gw, cell/f.gw
scan:
	for oy := -1; oy <= 1; oy++ {
		row := (gy + oy + f.gh) % f.gh
		for ox := -1; ox <= 1; ox++ {
			c := row*f.gw + (gx+ox+f.gw)%f.gw
			for j := f.cellStart[c]; j < f.cellStart[c+1]; j++ {
				if int(j) == k {
					continue
				}
				dx, dy := f.sx[j]-x, f.sy[j]-y
				if dx > hw {
					dx -= w
				} else if dx < -hw {
					dx += w
				}
				if dy > hh {
					dy -= h
				} else if dy < -hh {
					dy += h
				}
				d2 := dx*dx + dy*dy
				if d2 >= r2 {
					continue
				}
				count++
				avx += f.svx[j]
				avy += f.svy[j]
				cx += dx
				cy += dy
				if d2 < sep2 {
					inv := 1 / (d2 + 1)
					fx -= dx * inv
					fy -= dy * inv
				}
				if count >= p.MaxNeighbors {
					break scan
				}
			}
		}
	}

	var ax, ay float32
	if count > 0 {
		inv := 1 / float32(count)
		ax += (avx*inv - vx) * p.Alignment
		ay += (avy*inv - vy) * p.Alignment
		ax += cx * inv * p.Cohesion
		ay += cy * inv * p.Cohesion
		ax += fx * p.Separation
		ay += fy * p.Separation
	}
	flx, fly := f.flow(x, y)
	ax += (flx*p.MaxSpeed - vx) * p.Flow
	ay += (fly*p.MaxSpeed - vy) * p.Flow
	s := f.rng[i]
	ax += (unit(&s)*2 - 1) * p.Wander
	ay += (unit(&s)*2 - 1) * p.Wander
	f.rng[i] = s

	for _, im := range f.impulses {
		dx, dy := x-im.x, y-im.y
		d2 := dx*dx + dy*dy
		if d2 >= im.radius*im.radius || d2 == 0 {
			continue
		}
		d := float32(math.Sqrt(float64(d2)))
		push := im.strength * (1 - d/im.radius) / d
		vx += dx * push
		vy += dy * push
	}

	vx += ax * dt
	vy += ay * dt
	sp := float32(math.Sqrt(float64(vx*vx + vy*vy)))
	switch {
	case sp > p.MaxSpeed:
		// Impulses can push a boid past MaxSpeed. Let it slow back down
		// over about a second instead of clamping it at once.
		lim := max(p.MaxSpeed, sp-sp*dt*2)
		vx, vy = vx*lim/sp, vy*lim/sp
	case sp < p.MinSpeed && sp > 0:
		vx, vy = vx*p.MinSpeed/sp, vy*p.MinSpeed/sp
	}
	x = wrap(x+vx*dt, w)
	y = wrap(y+vy*dt, h)
	f.X[i], f.Y[i], f.VX[i], f.VY[i] = x, y, vx, vy
}

func wrap(v, size float32) float32 {
	if v < 0 {
		v += size
		if v < 0 {
			v = 0
		}
	} else if v >= size {
		v -= size
		if v >= size {
			v = 0
		}
	}
	return v
}

func xorshift(s uint32) uint32 {
	s ^= s << 13
	s ^= s >> 17
	s ^= s << 5
	return s
}

// unit advances s and returns a value in [0, 1).
func unit(s *uint32) float32 {
	*s = xorshift(*s)
	return float32(*s>>8) / (1 << 24)
}

func grow[T any](s []T, n int) []T {
	if cap(s) < n {
		return make([]T, n)
	}
	return s[:n]
}

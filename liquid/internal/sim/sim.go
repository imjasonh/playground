// Package sim simulates a 2D liquid as a set of particles.
//
// The solver is the double density relaxation method from Clavet, Beaudoin,
// and Poulin, "Particle-based Viscoelastic Fluid Simulation" (SCA 2005).
// Each step predicts particle positions from their velocities, then moves
// neighboring particles apart or together until the local density relaxes
// toward a rest density. A second, always-repulsive "near" density keeps
// particles from clumping and gives the liquid surface tension, so it forms
// droplets and splashes.
//
// Lengths are measured in units of the interaction radius h, so a particle
// interacts with every neighbor closer than 1. Time is in seconds.
package sim

import (
	"math"
	"math/rand/v2"
)

// Vec is a 2D vector.
type Vec struct{ X, Y float64 }

// Params are the material constants of the liquid.
type Params struct {
	// Gravity is the magnitude of gravity, in h/s².
	Gravity float64
	// RestDensity is the density that pressure relaxes toward.
	RestDensity float64
	// Stiffness scales the pressure that corrects density errors.
	Stiffness float64
	// NearStiffness scales the near pressure, which only pushes apart.
	NearStiffness float64
	// LinearViscosity and QuadraticViscosity damp the velocity at which
	// neighbors approach each other.
	LinearViscosity    float64
	QuadraticViscosity float64
	// MaxSpeed caps particle speed, in h/s, so a hard push can't explode the
	// liquid.
	MaxSpeed float64
	// The relaxation keeps resting liquid trembling at about 1 h/s. Particles
	// slower than SettleSpeed, in h/s, lose speed at up to SettleRate per
	// second, so liquid at rest comes to rest.
	SettleSpeed float64
	SettleRate  float64
	// PourRate is how many particles per second the pour tool emits.
	PourRate float64
}

// Spacing is the distance between particles when a scene is laid out, in h.
const Spacing = 0.42

// StepDuration is the step length, in seconds, that DefaultParams are tuned
// for. Longer steps make resting liquid tremble, and steps longer than about
// 1/60 s become unstable.
const StepDuration = 1.0 / 180

// cohesion sets how strongly the liquid holds together. Near pressure always
// pushes particles apart, so unless the rest density is above the density
// the particles are laid out at, nothing holds a free blob of liquid
// together. At the free surface of a half plane, the near pressure's push is
// half the pressure's for the same value, so a rest density of
//
//	ρ0 = ρ + cohesion · (kNear/k) · ρNear
//
// with cohesion = 0.5 balances them for liquid laid out at density ρ and near
// density ρNear. Gravity squeezes the liquid well past its layout density, so
// a smaller value is enough to keep a zero-gravity blob whole while leaving
// the liquid free to splash.
const cohesion = 0.2

// DefaultParams returns constants that look like water at the scale of a
// terminal.
func DefaultParams() Params {
	p := Params{
		Gravity:            140,
		Stiffness:          260,
		NearStiffness:      900,
		LinearViscosity:    16,
		QuadraticViscosity: 0.5,
		MaxSpeed:           45,
		SettleSpeed:        1.5,
		SettleRate:         54,
		PourRate:           240,
	}
	rho, rhoNear := latticeDensity(Spacing)
	p.RestDensity = rho + cohesion*(p.NearStiffness/p.Stiffness)*rhoNear
	return p
}

// latticeDensity returns the density and near density of a particle inside an
// unbounded triangular lattice with the given spacing, using the solver's
// kernels.
func latticeDensity(spacing float64) (rho, rhoNear float64) {
	rowHeight := spacing * math.Sqrt(3) / 2
	n := int(math.Ceil(1/rowHeight)) + 1
	for row := -n; row <= n; row++ {
		offset := 0.0
		if row%2 != 0 {
			offset = spacing / 2
		}
		for col := -n * 2; col <= n*2; col++ {
			r := math.Hypot(float64(col)*spacing+offset, float64(row)*rowHeight)
			if r == 0 || r >= 1 {
				continue
			}
			c := 1 - r
			rho += c * c
			rhoNear += c * c * c
		}
	}
	return rho, rhoNear
}

// Tool selects how the brush affects nearby particles.
type Tool int

// Brush tools.
const (
	// ToolNone leaves the liquid alone.
	ToolNone Tool = iota
	// ToolPush blasts particles away from the brush.
	ToolPush
	// ToolPull draws particles in and holds them as a blob under the brush.
	ToolPull
	// ToolAttract gently gathers particles toward the brush.
	ToolAttract
	// ToolDisperse gently scatters particles away from the brush.
	ToolDisperse
	// ToolPour emits new particles at the brush.
	ToolPour
)

// String returns the tool's name as shown in the interface.
func (t Tool) String() string {
	switch t {
	case ToolPush:
		return "push"
	case ToolPull:
		return "pull"
	case ToolAttract:
		return "attract"
	case ToolDisperse:
		return "disperse"
	case ToolPour:
		return "pour"
	default:
		return "none"
	}
}

// force describes how a tool accelerates particles inside the brush. Every
// term falls off linearly from the center of the brush to its edge.
type force struct {
	strength float64 // Acceleration toward the center, in h/s². Negative pushes.
	drag     float64 // Rate, in 1/s, at which particles match the cursor's velocity.
	lift     float64 // Rate at which gravity weakens toward the center; above 1, the core is weightless.
}

func (t Tool) force() force {
	switch t {
	case ToolPush:
		return force{strength: -1400, drag: 3}
	case ToolPull:
		return force{strength: 900, drag: 10, lift: 1.6}
	case ToolAttract:
		return force{strength: 260, drag: 4, lift: 0.6}
	case ToolDisperse:
		return force{strength: -420, drag: 1.5}
	default:
		return force{}
	}
}

// Brush is the cursor's influence on the liquid.
type Brush struct {
	Tool   Tool
	Pos    Vec     // Center of the brush, in h.
	Vel    Vec     // Velocity of the cursor, in h/s.
	Radius float64 // Radius of the brush, in h.
}

// World is a rectangular tank of liquid.
//
// The particle slices hold one entry per particle. Step reorders particles to
// keep neighbors close in memory, so a particle's index isn't stable across
// steps.
type World struct {
	Width, Height float64 // Size of the tank, in h.

	// Gravity is the direction of gravity, scaled by Params.Gravity. The zero
	// vector turns gravity off.
	Gravity Vec
	Params  Params
	Brush   Brush
	// MaxParticles caps how many particles the pour tool can add. Zero means no
	// limit.
	MaxParticles int

	X, Y   []float64 // Positions, in h.
	VX, VY []float64 // Velocities, in h/s.
	Dye    []float32 // A per-particle tag in [0, 1] that renderers can blend by.

	px, py []float64 // Positions at the start of the step.

	cell      []int32 // Grid cell of each particle.
	cellStart []int32 // Index of the first particle of each cell, plus a sentinel.
	gridW     int
	gridH     int
	perm      []int32
	scratch   []float64
	scratch32 []float32
	scratchI  []int32

	nbrStart []int32 // Offsets into nbrs for each particle, plus a sentinel.
	nbrs     []int32 // Indices of the particles closer than h, per particle.
	nbrValid bool

	pairs    []pair // Neighbor scratch for one particle during relaxation.
	reverse  bool   // Relaxation order, alternated to cancel sweep bias.
	pourDebt float64
	rng      *rand.Rand
}

type pair struct {
	j      int32
	c      float64 // 1 - r/h
	ux, uy float64 // Unit vector from particle i to particle j.
}

// New returns an empty tank with default parameters and downward gravity. The
// seed makes the random jitter used by scenes and collisions repeatable.
func New(width, height float64, seed uint64) *World {
	return &World{
		Width:   width,
		Height:  height,
		Gravity: Vec{0, 1},
		Params:  DefaultParams(),
		rng:     rand.New(rand.NewPCG(seed, 0x9e3779b97f4a7c15)),
	}
}

// Len returns the number of particles.
func (w *World) Len() int { return len(w.X) }

// Clear removes every particle.
func (w *World) Clear() {
	w.X, w.Y = w.X[:0], w.Y[:0]
	w.VX, w.VY = w.VX[:0], w.VY[:0]
	w.Dye = w.Dye[:0]
	w.px, w.py = w.px[:0], w.py[:0]
	w.nbrValid = false
}

// Add adds a particle at (x, y) with velocity (vx, vy). Positions outside the
// tank are moved inside it.
func (w *World) Add(x, y, vx, vy float64, dye float32) {
	x, y = w.clamp(x, y)
	w.X = append(w.X, x)
	w.Y = append(w.Y, y)
	w.VX = append(w.VX, vx)
	w.VY = append(w.VY, vy)
	w.Dye = append(w.Dye, dye)
	w.px = append(w.px, x)
	w.py = append(w.py, y)
	w.nbrValid = false
}

// Resize changes the size of the tank and moves particles that are now outside
// it back inside.
func (w *World) Resize(width, height float64) {
	w.Width, w.Height = width, height
	for i := range w.X {
		w.X[i], w.Y[i] = w.clamp(w.X[i], w.Y[i])
	}
	w.nbrValid = false
}

// Shake kicks every particle, mostly in the direction of dir, as if someone
// bumped the tank.
func (w *World) Shake(dir Vec, speed float64) {
	for i := range w.VX {
		w.VX[i] += dir.X*speed + (w.rng.Float64()-0.5)*speed*0.4
		w.VY[i] += dir.Y*speed + (w.rng.Float64()-0.5)*speed*0.4
	}
}

// Step advances the simulation by dt seconds. Callers split longer intervals
// into steps of StepDuration.
func (w *World) Step(dt float64) {
	if dt <= 0 {
		return
	}
	w.pour(dt)
	if len(w.X) == 0 {
		return
	}

	w.applyForces(dt)
	if !w.nbrValid {
		w.findNeighbors()
	}
	w.applyViscosity(dt)

	for i := range w.X {
		w.px[i], w.py[i] = w.X[i], w.Y[i]
		w.X[i] += w.VX[i] * dt
		w.Y[i] += w.VY[i] * dt
	}

	w.findNeighbors()
	w.relax(dt)
	w.collide()

	inv := 1 / dt
	maxSpeed := w.Params.MaxSpeed
	settle := w.Params.SettleSpeed
	settleFrac := min(1, w.Params.SettleRate*dt)
	for i := range w.X {
		vx := (w.X[i] - w.px[i]) * inv
		vy := (w.Y[i] - w.py[i]) * inv
		s := math.Sqrt(vx*vx + vy*vy)
		switch {
		case s > maxSpeed:
			vx *= maxSpeed / s
			vy *= maxSpeed / s
		case s < settle:
			f := 1 - (1-s/settle)*settleFrac
			vx *= f
			vy *= f
		}
		w.VX[i], w.VY[i] = vx, vy
	}
}

// applyForces accelerates particles by gravity and by the brush.
func (w *World) applyForces(dt float64) {
	gx := w.Gravity.X * w.Params.Gravity
	gy := w.Gravity.Y * w.Params.Gravity

	b := w.Brush
	f := b.Tool.force()
	active := b.Tool != ToolNone && b.Tool != ToolPour && b.Radius > 0
	r2 := b.Radius * b.Radius

	for i := range w.X {
		ax, ay := gx, gy
		if active {
			dx := b.Pos.X - w.X[i]
			dy := b.Pos.Y - w.Y[i]
			if d2 := dx*dx + dy*dy; d2 < r2 {
				d := math.Sqrt(d2)
				t := 1 - d/b.Radius
				lift := max(1-t*f.lift, 0)
				ax *= lift
				ay *= lift
				if d > 1e-9 {
					ax += dx / d * t * f.strength
					ay += dy / d * t * f.strength
				}
				ax += (b.Vel.X - w.VX[i]) * t * f.drag
				ay += (b.Vel.Y - w.VY[i]) * t * f.drag
			}
		}
		w.VX[i] += ax * dt
		w.VY[i] += ay * dt
	}
}

// pour emits particles at the brush while the pour tool is active.
func (w *World) pour(dt float64) {
	if w.Brush.Tool != ToolPour || w.Brush.Radius <= 0 {
		w.pourDebt = 0
		return
	}
	w.pourDebt += w.Params.PourRate * dt
	spread := math.Max(w.Brush.Radius*0.35, Spacing)
	for w.pourDebt >= 1 {
		if w.MaxParticles > 0 && len(w.X) >= w.MaxParticles {
			w.pourDebt = 0
			return
		}
		w.pourDebt--
		angle := w.rng.Float64() * 2 * math.Pi
		r := spread * math.Sqrt(w.rng.Float64())
		x := w.Brush.Pos.X + r*math.Cos(angle)
		y := w.Brush.Pos.Y + r*math.Sin(angle)
		vx := w.Brush.Vel.X*0.6 + w.Gravity.X*4
		vy := w.Brush.Vel.Y*0.6 + w.Gravity.Y*4
		w.Add(x, y, vx, vy, w.rng.Float32())
	}
}

// findNeighbors sorts particles into grid cells of size h and records, for
// each particle, every other particle closer than h.
func (w *World) findNeighbors() {
	n := len(w.X)
	gw := max(1, int(math.Ceil(w.Width)))
	gh := max(1, int(math.Ceil(w.Height)))
	cells := gw * gh
	w.gridW, w.gridH = gw, gh

	w.cell = grow(w.cell, n)
	w.cellStart = grow(w.cellStart, cells+1)
	clear(w.cellStart)
	for i := range n {
		cx := min(max(int(w.X[i]), 0), gw-1)
		cy := min(max(int(w.Y[i]), 0), gh-1)
		c := int32(cy*gw + cx)
		w.cell[i] = c
		w.cellStart[c+1]++
	}
	for c := range cells {
		w.cellStart[c+1] += w.cellStart[c]
	}

	// Counting sort: perm[dst] is the old index of the particle that moves to
	// dst. scratchI tracks the next free slot of each cell.
	w.perm = grow(w.perm, n)
	w.scratchI = grow(w.scratchI, cells)
	copy(w.scratchI, w.cellStart[:cells])
	for i := range n {
		c := w.cell[i]
		w.perm[w.scratchI[c]] = int32(i)
		w.scratchI[c]++
	}
	w.permute()

	w.nbrStart = grow(w.nbrStart, n+1)
	w.nbrs = w.nbrs[:0]
	for i := range n {
		w.nbrStart[i] = int32(len(w.nbrs))
		xi, yi := w.X[i], w.Y[i]
		c := int(w.cell[i])
		cx, cy := c%gw, c/gw
		for ny := max(cy-1, 0); ny <= min(cy+1, gh-1); ny++ {
			row := ny * gw
			lo := w.cellStart[row+max(cx-1, 0)]
			hi := w.cellStart[row+min(cx+1, gw-1)+1]
			for j := lo; j < hi; j++ {
				if int(j) == i {
					continue
				}
				dx := w.X[j] - xi
				dy := w.Y[j] - yi
				if dx*dx+dy*dy < 1 {
					w.nbrs = append(w.nbrs, j)
				}
			}
		}
	}
	w.nbrStart[n] = int32(len(w.nbrs))
	w.nbrValid = true
}

// permute reorders every per-particle slice by w.perm.
func (w *World) permute() {
	n := len(w.X)
	w.scratch = grow(w.scratch, n)
	for _, s := range []*[]float64{&w.X, &w.Y, &w.VX, &w.VY, &w.px, &w.py} {
		src := *s
		for dst, from := range w.perm[:n] {
			w.scratch[dst] = src[from]
		}
		*s, w.scratch = w.scratch, src
	}
	w.scratch32 = grow(w.scratch32, n)
	for dst, from := range w.perm[:n] {
		w.scratch32[dst] = w.Dye[from]
	}
	w.Dye, w.scratch32 = w.scratch32, w.Dye

	cells := w.cell[:n]
	w.scratchI = grow(w.scratchI, n)
	for dst, from := range w.perm[:n] {
		w.scratchI[dst] = cells[from]
	}
	w.cell, w.scratchI = w.scratchI, w.cell
}

// applyViscosity damps the velocity at which neighbors approach each other.
// It uses the neighbor lists from the end of the previous step.
func (w *World) applyViscosity(dt float64) {
	sigma := w.Params.LinearViscosity
	beta := w.Params.QuadraticViscosity
	if sigma == 0 && beta == 0 {
		return
	}
	for i := range w.X {
		xi, yi := w.X[i], w.Y[i]
		for _, j := range w.nbrs[w.nbrStart[i]:w.nbrStart[i+1]] {
			if int(j) <= i {
				continue
			}
			dx := w.X[j] - xi
			dy := w.Y[j] - yi
			d2 := dx*dx + dy*dy
			if d2 >= 1 || d2 < 1e-18 {
				continue
			}
			r := math.Sqrt(d2)
			ux, uy := dx/r, dy/r
			u := (w.VX[i]-w.VX[j])*ux + (w.VY[i]-w.VY[j])*uy
			if u <= 0 {
				continue
			}
			imp := 0.5 * dt * (1 - r) * (sigma*u + beta*u*u)
			w.VX[i] -= imp * ux
			w.VY[i] -= imp * uy
			w.VX[j] += imp * ux
			w.VY[j] += imp * uy
		}
	}
}

// relax runs one pass of double density relaxation, moving each particle and
// its neighbors so the local density approaches the rest density.
func (w *World) relax(dt float64) {
	dt2 := dt * dt
	k := w.Params.Stiffness
	kNear := w.Params.NearStiffness
	rho0 := w.Params.RestDensity

	n := len(w.X)
	wt := walls()
	w.reverse = !w.reverse
	for step := range n {
		i := step
		if w.reverse {
			i = n - 1 - step
		}
		xi, yi := w.X[i], w.Y[i]

		// Distances to the left, right, top, and bottom walls, and the wall
		// terms for each wall closer than h.
		var wallPush, wallPushNear [4]float64
		var rho, rhoNear float64
		wallD := [4]float64{xi, w.Width - xi, yi, w.Height - yi}
		for side, d := range wallD {
			if d >= 1 {
				continue
			}
			r, rn, p, pn := wt.at(d)
			rho += r
			rhoNear += rn
			wallPush[side], wallPushNear[side] = p, pn
		}

		w.pairs = w.pairs[:0]
		for _, j := range w.nbrs[w.nbrStart[i]:w.nbrStart[i+1]] {
			dx := w.X[j] - xi
			dy := w.Y[j] - yi
			d2 := dx*dx + dy*dy
			if d2 >= 1 {
				continue
			}
			if d2 < 1e-12 {
				// Two particles at the same spot have no direction to separate
				// along, so nudge one of them.
				w.X[j] += (w.rng.Float64() - 0.5) * 1e-3
				w.Y[j] += (w.rng.Float64() - 0.5) * 1e-3
				continue
			}
			r := math.Sqrt(d2)
			c := 1 - r
			rho += c * c
			rhoNear += c * c * c
			w.pairs = append(w.pairs, pair{j: j, c: c, ux: dx / r, uy: dy / r})
		}

		p := k * (rho - rho0)
		pNear := kNear * rhoNear
		var dxi, dyi float64
		for _, pr := range w.pairs {
			d := 0.5 * dt2 * (p*pr.c + pNear*pr.c*pr.c)
			mx, my := d*pr.ux, d*pr.uy
			w.X[pr.j] += mx
			w.Y[pr.j] += my
			dxi -= mx
			dyi -= my
		}

		// Walls only push. Letting low pressure pull particles toward a wall
		// would make the liquid cling to the ceiling. A wall can't move, so the
		// particle takes the whole displacement instead of half.
		wallP := max(p, 0)
		for side, push := range wallPush {
			if push == 0 && wallPushNear[side] == 0 {
				continue
			}
			d := dt2 * (wallP*push + pNear*wallPushNear[side])
			switch side {
			case 0:
				dxi += d
			case 1:
				dxi -= d
			case 2:
				dyi += d
			case 3:
				dyi -= d
			}
		}
		w.X[i] += dxi
		w.Y[i] += dyi
	}
}

// wallMargin keeps particles a hair inside the walls so that particles pressed
// against the same wall don't land on exactly the same coordinate.
const wallMargin = 1e-3

// collide moves particles that left the tank back inside. Their velocity
// into the wall drops to zero when Step derives velocity from position.
func (w *World) collide() {
	maxX := w.Width - wallMargin
	maxY := w.Height - wallMargin
	for i := range w.X {
		if x := w.X[i]; x < wallMargin {
			w.X[i] = wallMargin + w.rng.Float64()*wallMargin
		} else if x > maxX {
			w.X[i] = maxX - w.rng.Float64()*wallMargin
		}
		if y := w.Y[i]; y < wallMargin {
			w.Y[i] = wallMargin + w.rng.Float64()*wallMargin
		} else if y > maxY {
			w.Y[i] = maxY - w.rng.Float64()*wallMargin
		}
	}
}

func (w *World) clamp(x, y float64) (float64, float64) {
	return min(max(x, wallMargin), w.Width-wallMargin), min(max(y, wallMargin), w.Height-wallMargin)
}

// grow returns s resized to n elements, reusing its backing array when it is
// large enough.
func grow[T any](s []T, n int) []T {
	if cap(s) < n {
		return make([]T, n, n+n/4)
	}
	return s[:n]
}

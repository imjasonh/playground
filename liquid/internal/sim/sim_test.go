package sim

import (
	"math"
	"math/rand/v2"
	"slices"
	"testing"
)

// run steps w for the given number of seconds.
func run(w *World, seconds float64) {
	for range int(seconds / StepDuration) {
		w.Step(StepDuration)
	}
}

// countWithin returns how many particles are closer than r to (x, y).
func countWithin(w *World, x, y, r float64) int {
	n := 0
	for i := range w.X {
		if math.Hypot(w.X[i]-x, w.Y[i]-y) < r {
			n++
		}
	}
	return n
}

func meanSpeed(w *World) float64 {
	var sum float64
	for i := range w.VX {
		sum += math.Hypot(w.VX[i], w.VY[i])
	}
	return sum / float64(len(w.VX))
}

func checkInside(t *testing.T, w *World) {
	t.Helper()
	for i := range w.X {
		x, y := w.X[i], w.Y[i]
		if math.IsNaN(x) || math.IsNaN(y) || math.IsNaN(w.VX[i]) || math.IsNaN(w.VY[i]) {
			t.Fatalf("particle %d is NaN: (%v, %v) moving (%v, %v)", i, x, y, w.VX[i], w.VY[i])
		}
		if x < 0 || x > w.Width || y < 0 || y > w.Height {
			t.Fatalf("particle %d at (%v, %v) is outside the %v×%v tank", i, x, y, w.Width, w.Height)
		}
	}
}

func TestNeighborsMatchBruteForce(t *testing.T) {
	t.Parallel()
	w := New(12, 9, 3)
	r := rand.New(rand.NewPCG(1, 2))
	for range 600 {
		w.Add(r.Float64()*w.Width, r.Float64()*w.Height, 0, 0, 0)
	}
	w.findNeighbors()
	for i := range w.X {
		got := slices.Clone(w.nbrs[w.nbrStart[i]:w.nbrStart[i+1]])
		var want []int32
		for j := range w.X {
			if j != i && math.Hypot(w.X[j]-w.X[i], w.Y[j]-w.Y[i]) < 1 {
				want = append(want, int32(j))
			}
		}
		slices.Sort(got)
		if !slices.Equal(got, want) {
			t.Fatalf("particle %d: neighbors %v, want %v", i, got, want)
		}
	}
}

func TestDamBreakFlowsAndStaysInTank(t *testing.T) {
	t.Parallel()
	w := New(28, 16, 1)
	w.Populate(SceneDam)
	n := w.Len()
	if n < 500 {
		t.Fatalf("dam break has %d particles, want at least 500", n)
	}
	run(w, 1)
	checkInside(t, w)
	if far := countWithin(w, w.Width, w.Height, w.Width*0.4); far < n/20 {
		t.Errorf("after 1s, %d particles reached the far side of the tank, want at least %d", far, n/20)
	}
	if w.Len() != n {
		t.Errorf("particle count changed from %d to %d", n, w.Len())
	}
}

func TestPoolComesToRest(t *testing.T) {
	t.Parallel()
	w := New(28, 16, 1)
	w.Populate(ScenePool)
	run(w, 4)
	checkInside(t, w)
	if s := meanSpeed(w); s > 0.5 {
		t.Errorf("mean speed after 4s is %.2f h/s, want the pool at rest (under 0.5)", s)
	}
	var top float64 = w.Height
	for _, y := range w.Y {
		top = min(top, y)
	}
	if top < w.Height*0.35 {
		t.Errorf("liquid reaches y=%.1f, want the pool to stay in the bottom of the %.0fh tank", top, w.Height)
	}
}

func TestZeroGravityBlobHoldsTogether(t *testing.T) {
	t.Parallel()
	w := New(28, 16, 1)
	w.Populate(SceneBlob)
	if w.Gravity != (Vec{}) {
		t.Fatalf("blob scene gravity is %v, want none", w.Gravity)
	}
	n := w.Len()
	run(w, 3)
	checkInside(t, w)
	r := math.Sqrt(0.24*w.Width*w.Height/math.Pi) + 1.5
	if in := countWithin(w, w.Width/2, w.Height/2, r); in < n*9/10 {
		t.Errorf("%d of %d particles stayed in the blob, want at least 90%%", in, n)
	}
}

func TestBrushTools(t *testing.T) {
	t.Parallel()
	for _, tc := range []struct {
		tool Tool
		more bool // Whether the tool should gather particles into the brush.
	}{
		{ToolPush, false},
		{ToolDisperse, false},
		{ToolPull, true},
		{ToolAttract, true},
	} {
		t.Run(tc.tool.String(), func(t *testing.T) {
			t.Parallel()
			w := New(28, 16, 1)
			w.Populate(ScenePool)
			run(w, 1)
			// Aim at the surface, so the brush covers both liquid and air.
			surface := w.Height * 0.55
			center := Vec{w.Width / 2, surface}
			const radius = 4.0
			before := countWithin(w, center.X, center.Y, radius*0.6)
			w.Brush = Brush{Tool: tc.tool, Pos: center, Radius: radius}
			run(w, 0.75)
			checkInside(t, w)
			after := countWithin(w, center.X, center.Y, radius*0.6)
			if tc.more && after <= before*5/4 {
				t.Errorf("%v: %d particles near the brush, then %d; want more", tc.tool, before, after)
			}
			if !tc.more && after >= before/2 {
				t.Errorf("%v: %d particles near the brush, then %d; want fewer than half", tc.tool, before, after)
			}
		})
	}
}

func TestPushIsStrongerThanDisperse(t *testing.T) {
	t.Parallel()
	cleared := func(tool Tool) int {
		w := New(28, 16, 1)
		w.Populate(ScenePool)
		run(w, 1)
		center := Vec{w.Width / 2, w.Height * 0.8}
		w.Brush = Brush{Tool: tool, Pos: center, Radius: 4}
		run(w, 0.3)
		return countWithin(w, center.X, center.Y, 2)
	}
	if push, disperse := cleared(ToolPush), cleared(ToolDisperse); push >= disperse {
		t.Errorf("push left %d particles in the brush, disperse left %d; want push to clear more", push, disperse)
	}
}

func TestPourAddsParticlesUpToLimit(t *testing.T) {
	t.Parallel()
	w := New(24, 16, 1)
	w.Populate(ScenePool)
	n := w.Len()
	w.MaxParticles = n + 100
	w.Brush = Brush{Tool: ToolPour, Pos: Vec{12, 3}, Radius: 3}
	run(w, 0.2)
	if w.Len() <= n {
		t.Fatalf("pour added no particles: still %d", w.Len())
	}
	run(w, 2)
	checkInside(t, w)
	if w.Len() != n+100 {
		t.Errorf("after pouring past the limit, have %d particles, want %d", w.Len(), n+100)
	}
}

func TestResizeMovesParticlesInside(t *testing.T) {
	t.Parallel()
	w := New(28, 16, 1)
	w.Populate(SceneDam)
	run(w, 0.5)
	w.Resize(16, 11)
	checkInside(t, w)
	run(w, 0.5)
	checkInside(t, w)
}

func TestGravityDirection(t *testing.T) {
	t.Parallel()
	w := New(20, 20, 1)
	w.Populate(SceneBlob)
	w.Gravity = Vec{1, 0}
	run(w, 2)
	var sum float64
	for _, x := range w.X {
		sum += x
	}
	if mean := sum / float64(w.Len()); mean < w.Width*0.7 {
		t.Errorf("with gravity pointing right, the liquid's mean x is %.1f, want it against the right wall (> %.1f)", mean, w.Width*0.7)
	}
}

func TestDeterministic(t *testing.T) {
	t.Parallel()
	a, b := New(20, 15, 42), New(20, 15, 42)
	for _, w := range []*World{a, b} {
		w.Populate(SceneDrop)
		w.Brush = Brush{Tool: ToolPush, Pos: Vec{10, 10}, Radius: 3}
		run(w, 0.5)
	}
	if !slices.Equal(a.X, b.X) || !slices.Equal(a.Y, b.Y) {
		t.Error("two worlds with the same seed and inputs diverged")
	}
}

func TestShakeMovesLiquid(t *testing.T) {
	t.Parallel()
	w := New(24, 14, 1)
	w.Populate(ScenePool)
	run(w, 2)
	w.Shake(Vec{1, -0.5}, 16)
	if s := meanSpeed(w); s < 10 {
		t.Errorf("after a shake, mean speed is %.1f h/s, want at least 10", s)
	}
	run(w, 1)
	checkInside(t, w)
}

func TestScenesStartAtLatticeDensity(t *testing.T) {
	t.Parallel()
	for _, s := range Scenes {
		t.Run(s.Short(), func(t *testing.T) {
			t.Parallel()
			w := New(40, 22, 1)
			w.Populate(s)
			if w.Len() == 0 {
				t.Fatal("scene is empty")
			}
			// Measure the density of particles well inside the liquid.
			w.findNeighbors()
			var sum float64
			var n int
			for i := range w.X {
				if w.nbrStart[i+1]-w.nbrStart[i] < 18 {
					continue
				}
				var rho float64
				for _, j := range w.nbrs[w.nbrStart[i]:w.nbrStart[i+1]] {
					c := 1 - math.Hypot(w.X[j]-w.X[i], w.Y[j]-w.Y[i])
					rho += c * c
				}
				sum += rho
				n++
			}
			if n == 0 {
				t.Fatal("no particles inside the liquid")
			}
			want, _ := latticeDensity(Spacing)
			if got := sum / float64(n); math.Abs(got-want) > want*0.1 {
				t.Errorf("interior density is %.2f, want within 10%% of the lattice density %.2f", got, want)
			}
		})
	}
}

func TestWallTable(t *testing.T) {
	t.Parallel()
	wt := newWallTable(Spacing)
	prev := math.Inf(1)
	for d := 0.0; d < 1; d += 0.05 {
		rho, rhoNear, push, pushNear := wt.at(d)
		if rho <= 0 || rhoNear <= 0 || push <= 0 || pushNear <= 0 {
			t.Fatalf("at d=%.2f, wall terms are %v %v %v %v, want all positive", d, rho, rhoNear, push, pushNear)
		}
		if rho >= prev {
			t.Fatalf("wall density at d=%.2f is %v, want it to fall with distance (previous %v)", d, rho, prev)
		}
		prev = rho
	}
	if rho, _, _, _ := wt.at(1); rho != 0 {
		t.Errorf("wall density at d=1 is %v, want 0", rho)
	}
}

func BenchmarkStep(b *testing.B) {
	w := New(40, 22, 1)
	w.Populate(SceneDam)
	run(w, 1)
	b.ResetTimer()
	for b.Loop() {
		w.Step(StepDuration)
	}
	b.ReportMetric(float64(w.Len()), "particles")
}

package flock

import (
	"fmt"
	"math"
	"slices"
	"testing"
)

func TestSortGroupsByCell(t *testing.T) {
	f := New(1920, 1080, DefaultParams(), 4, 7)
	f.Resize(5000)
	f.sort()
	seen := make([]bool, f.Len())
	for c := 0; c < f.gw*f.gh; c++ {
		for k := f.cellStart[c]; k < f.cellStart[c+1]; k++ {
			i := f.order[k]
			if got := f.cellOf[i]; got != int32(c) {
				t.Fatalf("boid %d sorted into cell %d, belongs in %d", i, c, got)
			}
			if seen[i] {
				t.Fatalf("boid %d sorted twice", i)
			}
			seen[i] = true
			if f.sx[k] != f.X[i] || f.svy[k] != f.VY[i] {
				t.Fatalf("sorted copy of boid %d does not match", i)
			}
		}
	}
	if i := slices.Index(seen, false); i >= 0 {
		t.Fatalf("boid %d missing from the grid", i)
	}
}

func TestStepIsIndependentOfWorkers(t *testing.T) {
	run := func(workers int) *Flock {
		f := New(1280, 720, DefaultParams(), workers, 42)
		f.Resize(3000)
		for s := range 120 {
			if s == 30 {
				f.Kick(640, 360, 200, 400)
			}
			f.Step(1.0 / 60)
		}
		return f
	}
	a, b := run(1), run(8)
	for i := range a.Len() {
		if a.X[i] != b.X[i] || a.Y[i] != b.Y[i] || a.VX[i] != b.VX[i] || a.VY[i] != b.VY[i] {
			t.Fatalf("boid %d differs between 1 and 8 workers: (%v,%v) vs (%v,%v)", i, a.X[i], a.Y[i], b.X[i], b.Y[i])
		}
	}
}

func TestBoidsStayInWorldAndInSpeedRange(t *testing.T) {
	p := DefaultParams()
	f := New(1920, 1080, p, 4, 3)
	f.Resize(2000)
	for range 600 {
		f.Step(1.0 / 60)
	}
	for i := range f.Len() {
		if f.X[i] < 0 || f.X[i] >= f.Width || f.Y[i] < 0 || f.Y[i] >= f.Height {
			t.Fatalf("boid %d left the world: (%v, %v)", i, f.X[i], f.Y[i])
		}
		sp := math.Hypot(float64(f.VX[i]), float64(f.VY[i]))
		if sp < float64(p.MinSpeed)-0.01 || sp > float64(p.MaxSpeed)+0.01 {
			t.Fatalf("boid %d speed %v outside [%v, %v]", i, sp, p.MinSpeed, p.MaxSpeed)
		}
	}
}

// TestFlockFormsStreams checks that after a while boids fly with their
// neighbors, the flock covers the screen instead of collapsing into a
// clump, and it doesn't settle on one heading.
func TestFlockFormsStreams(t *testing.T) {
	f := New(1920, 1080, DefaultParams(), 8, 11)
	f.Resize(3000)
	for range 60 * 20 {
		f.Step(1.0 / 60)
	}
	type sum struct {
		x, y float64
		n    int
	}
	var global sum
	cells := map[[2]int]*sum{}
	for i := range f.Len() {
		s := math.Hypot(float64(f.VX[i]), float64(f.VY[i]))
		ux, uy := float64(f.VX[i])/s, float64(f.VY[i])/s
		global.x += ux
		global.y += uy
		key := [2]int{int(f.X[i]) / 40, int(f.Y[i]) / 40}
		c := cells[key]
		if c == nil {
			c = &sum{}
			cells[key] = c
		}
		c.x += ux
		c.y += uy
		c.n++
	}
	var local float64
	var crowded int
	for _, c := range cells {
		if c.n >= 3 {
			local += math.Hypot(c.x, c.y) / float64(c.n)
			crowded++
		}
	}
	local /= float64(crowded)
	heading := math.Hypot(global.x, global.y) / float64(f.Len())
	// The screen is 48x27 cells of 40px.
	if len(cells) < 48*27/2 {
		t.Errorf("flock covers %d of %d cells, want at least half", len(cells), 48*27)
	}
	if local < 0.8 {
		t.Errorf("mean alignment within a cell = %.2f, want at least 0.8", local)
	}
	if heading > 0.6 {
		t.Errorf("mean alignment of the whole flock = %.2f, want at most 0.6", heading)
	}
}

func TestKickPushesAway(t *testing.T) {
	f := New(1000, 1000, DefaultParams(), 1, 5)
	f.Resize(1)
	f.X[0], f.Y[0], f.VX[0], f.VY[0] = 510, 500, 100, 0
	f.Kick(500, 500, 100, 1000)
	f.Step(1.0 / 60)
	if f.VX[0] <= 100 {
		t.Errorf("VX after kick = %v, want more than 100", f.VX[0])
	}
	// The kick is used once.
	v := f.VX[0]
	f.Step(1.0 / 60)
	if f.VX[0] > v {
		t.Errorf("VX grew again after the kick was used: %v > %v", f.VX[0], v)
	}
}

func TestSwap(t *testing.T) {
	f := New(800, 600, DefaultParams(), 1, 3)
	f.Resize(3)
	x0, vy2 := f.X[0], f.VY[2]
	f.Swap(0, 2)
	if f.X[2] != x0 || f.VY[0] != vy2 {
		t.Errorf("Swap didn't exchange boids 0 and 2")
	}
}

func TestResizeKeepsExistingBoids(t *testing.T) {
	f := New(800, 600, DefaultParams(), 2, 9)
	f.Resize(100)
	x5, y5 := f.X[5], f.Y[5]
	f.Resize(10)
	if f.Len() != 10 || f.X[5] != x5 || f.Y[5] != y5 {
		t.Fatalf("shrinking changed the boids that stayed")
	}
	f.Resize(50)
	if f.Len() != 50 || f.X[5] != x5 {
		t.Fatalf("growing changed the boids that were there")
	}
	f.Resize(0)
	f.Step(1.0 / 60)
}

func BenchmarkStep(b *testing.B) {
	for _, n := range []int{1000, 10000, 30000, 60000} {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			f := New(1920, 1080, DefaultParams(), 8, 1)
			f.Resize(n)
			for range 600 {
				f.Step(1.0 / 60)
			}
			b.ResetTimer()
			for b.Loop() {
				f.Step(1.0 / 60)
			}
		})
	}
}

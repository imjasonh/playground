package frame

import (
	"bytes"
	"fmt"
	"math/rand/v2"
	"strings"
	"testing"

	"github.com/imjasonh/playground/stream-boids/internal/flock"
	"golang.org/x/image/font/gofont/gomedium"
)

func TestFadeMatchesFormula(t *testing.T) {
	rng := rand.New(rand.NewPCG(1, 2))
	for n := range 40 {
		fb, bg := make([]byte, n), make([]byte, n)
		for i := range n {
			fb[i], bg[i] = byte(rng.IntN(256)), byte(rng.IntN(256))
		}
		want := make([]byte, n)
		for i := range n {
			want[i] = fadeByte(fb[i], bg[i])
		}
		fade(fb, bg)
		if !bytes.Equal(fb, want) {
			t.Fatalf("fade of %d bytes = %v, want %v", n, fb, want)
		}
	}
	// Every pair of byte values, eight at a time.
	fb, bg := make([]byte, 8), make([]byte, 8)
	for a := range 256 {
		for b := range 256 {
			for i := range 8 {
				fb[i], bg[i] = byte(a), byte(b)
			}
			fade(fb, bg)
			want := byte((a*224 + b*32) >> 8)
			if a < b {
				want++
			}
			if fb[3] != want {
				t.Fatalf("fade(%d, %d) = %d, want %d", a, b, fb[3], want)
			}
		}
	}
}

// TestFadeReachesBackground checks that every value fades all the way to
// every background value without passing it.
func TestFadeReachesBackground(t *testing.T) {
	for a := range 256 {
		for b := range 256 {
			f, steps := byte(a), 0
			for f != byte(b) {
				next := fadeByte(f, byte(b))
				lo, hi := min(f, byte(b)), max(f, byte(b))
				if next == f || next < lo || next > hi {
					t.Fatalf("fading %d toward %d: %d became %d", a, b, f, next)
				}
				f = next
				if steps++; steps > 64 {
					t.Fatalf("%d did not reach %d in 64 steps", a, b)
				}
			}
		}
	}
}

func TestRGB(t *testing.T) {
	for _, tc := range []struct {
		r, g, b uint8
		want    YUV
	}{
		{0, 0, 0, YUV{16, 128, 128}},
		{255, 255, 255, YUV{235, 128, 128}},
		{255, 0, 0, YUV{63, 102, 240}},
		{0, 0, 255, YUV{32, 240, 118}},
	} {
		if got := RGB(tc.r, tc.g, tc.b); got != tc.want {
			t.Errorf("RGB(%d, %d, %d) = %v, want %v", tc.r, tc.g, tc.b, got, tc.want)
		}
	}
}

func TestNewRejectsOddSizes(t *testing.T) {
	for _, sz := range [][2]int{{0, 16}, {1920, 1081}, {101, 100}, {-16, 16}} {
		if _, err := New(sz[0], sz[1]); err == nil {
			t.Errorf("New(%d, %d) succeeded, want an error", sz[0], sz[1])
		}
	}
}

func TestThousands(t *testing.T) {
	for n, want := range map[int]string{0: "0", 7: "7", 999: "999", 1000: "1,000", 123456: "123,456", 1234567: "1,234,567", -4321: "-4,321"} {
		if got := thousands(n); got != want {
			t.Errorf("thousands(%d) = %q, want %q", n, got, want)
		}
	}
}

func TestCleanName(t *testing.T) {
	tf, err := newTypeface(gomedium.TTF, 18)
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct{ in, want string }{
		{"Alice", "Alice"},
		{"  Bob   the\tBuilder ", "Bob the Builder"},
		{"evil\u202Eeman", "evileman"},
		{"null\x00byte\x1b[31m", "nullbyte[31m"},
		{"zero\u200Bwidth", "zerowidth"},
		{"bad\xffutf8", "badutf8"},
		{"\U0001F600 smile", "? smile"},
		{strings.Repeat("a", 30), strings.Repeat("a", 24) + "…"},
		{strings.Repeat("ab ", 10), "ab ab ab ab ab ab ab ab…"},
		{"", ""},
	} {
		if got := tf.cleanName(tc.in); got != tc.want {
			t.Errorf("cleanName(%q) = %q, want %q", tc.in, got, tc.want)
		}
	}
}

func newScene(t testing.TB, n int, labels ...string) *Scene {
	t.Helper()
	fl := flock.New(1280, 720, flock.DefaultParams(), 4, 99)
	fl.Resize(n)
	return &Scene{Flock: fl, Labels: labels, HUD: HUD{Viewers: n, ViewersKnown: true, Members: len(labels)}}
}

func newRenderer(t testing.TB, w, h, workers int) (*Renderer, *Frame) {
	t.Helper()
	r, err := NewRenderer(w, h, workers)
	if err != nil {
		t.Fatal(err)
	}
	out, err := New(w, h)
	if err != nil {
		t.Fatal(err)
	}
	return r, out
}

func TestRenderIsIndependentOfWorkers(t *testing.T) {
	sc := newScene(t, 4000, "alice", "bob", "carol")
	sc.Banner = &Banner{Name: "dave", Amount: "$20.00", Tier: 4}
	r1, out1 := newRenderer(t, 1280, 720, 1)
	r8, out8 := newRenderer(t, 1280, 720, 8)
	for f := range 30 {
		sc.Flock.Step(1.0 / 60)
		if err := r1.Render(sc, out1); err != nil {
			t.Fatal(err)
		}
		if err := r8.Render(sc, out8); err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(out1.Bytes(), out8.Bytes()) {
			t.Fatalf("frame %d differs between 1 and 8 workers", f)
		}
	}
}

func at(f *Frame, x, y int) YUV {
	return YUV{f.Y[y*f.W+x], f.U[(y/2)*(f.W/2)+x/2], f.V[(y/2)*(f.W/2)+x/2]}
}

func TestRenderDrawsMembersInGold(t *testing.T) {
	sc := newScene(t, 2, "alice")
	fl := sc.Flock
	fl.X[0], fl.Y[0], fl.VX[0], fl.VY[0] = 400, 400, 100, 0
	fl.X[1], fl.Y[1], fl.VX[1], fl.VY[1] = 900, 400, 100, 0
	r, out := newRenderer(t, 1280, 720, 4)
	if err := r.Render(sc, out); err != nil {
		t.Fatal(err)
	}
	if got := at(out, 400, 400); got != gold {
		t.Errorf("member boid color = %v, want gold %v", got, gold)
	}
	if got, want := at(out, 900, 400), r.palette[r.color[1]]; got != want {
		t.Errorf("viewer boid color = %v, want %v", got, want)
	}
	if _, ok := r.label.cache["alice"]; !ok {
		t.Errorf("member label was not drawn")
	}
}

func TestRenderHUDText(t *testing.T) {
	for _, tc := range []struct {
		hud            HUD
		viewers, membs string
	}{
		{HUD{Viewers: 1234, ViewersKnown: true, Members: 12}, "1,234 viewers", "12 members watching"},
		{HUD{Viewers: 1, ViewersKnown: true, Members: 1}, "1 viewer", "1 member watching"},
		{HUD{}, "-- viewers", "0 members watching"},
	} {
		sc := newScene(t, 10)
		sc.HUD = tc.hud
		r, out := newRenderer(t, 1280, 720, 2)
		if err := r.Render(sc, out); err != nil {
			t.Fatal(err)
		}
		if _, ok := r.big.cache[tc.viewers]; !ok {
			t.Errorf("HUD %+v: no %q in %v", tc.hud, tc.viewers, keys(r.big.cache))
		}
		if _, ok := r.small.cache[tc.membs]; !ok {
			t.Errorf("HUD %+v: no %q in %v", tc.hud, tc.membs, keys(r.small.cache))
		}
	}
}

func keys[V any](m map[string]V) []string {
	var ks []string
	for k := range m {
		ks = append(ks, k)
	}
	return ks
}

// TestOverlaysLeaveNoTrail renders a banner on one frame and checks that
// the next frame is the same as if the banner had never been shown.
func TestOverlaysLeaveNoTrail(t *testing.T) {
	sc := newScene(t, 500)
	ra, outA := newRenderer(t, 1280, 720, 4)
	rb, outB := newRenderer(t, 1280, 720, 4)
	sc.Banner = &Banner{Name: "erin", Tier: 7}
	if err := ra.Render(sc, outA); err != nil {
		t.Fatal(err)
	}
	sc.Banner = nil
	if err := rb.Render(sc, outB); err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(outA.Bytes(), outB.Bytes()) {
		t.Fatal("banner changed nothing")
	}
	if _, ok := ra.small.cache["erin sent a Super Sticker"]; !ok {
		t.Errorf("no sticker banner text in %v", keys(ra.small.cache))
	}
	sc.Flock.Step(1.0 / 60)
	if err := ra.Render(sc, outA); err != nil {
		t.Fatal(err)
	}
	if err := rb.Render(sc, outB); err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(outA.Bytes(), outB.Bytes()) {
		t.Error("banner left marks on the next frame")
	}
}

func TestRenderRejectsWrongSize(t *testing.T) {
	r, _ := newRenderer(t, 1280, 720, 1)
	out, err := New(640, 480)
	if err != nil {
		t.Fatal(err)
	}
	if err := r.Render(newScene(t, 1), out); err == nil {
		t.Error("Render into a smaller frame succeeded")
	}
}

func TestRenderEmptyFlock(t *testing.T) {
	r, out := newRenderer(t, 1280, 720, 4)
	if err := r.Render(newScene(t, 0, "ghost"), out); err != nil {
		t.Fatal(err)
	}
}

// BenchmarkFrame measures one simulation step plus one render at 1080p,
// the work the stream does for each frame.
func BenchmarkFrame(b *testing.B) {
	for _, n := range []int{1000, 10000, 30000, 60000} {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			fl := flock.New(1920, 1080, flock.DefaultParams(), 8, 1)
			fl.Resize(n)
			labels := make([]string, min(n, 200))
			for i := range labels {
				labels[i] = fmt.Sprintf("member %d", i)
			}
			sc := &Scene{Flock: fl, Labels: labels, HUD: HUD{Viewers: n, ViewersKnown: true, Members: len(labels)}}
			r, out := newRenderer(b, 1920, 1080, 8)
			for b.Loop() {
				fl.Step(1.0 / 60)
				if err := r.Render(sc, out); err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}

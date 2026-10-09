package render

import (
	"strings"
	"testing"

	"github.com/charmbracelet/x/ansi"

	"github.com/imjasonh/playground/liquid/internal/sim"
)

const cols, rows = 80, 24

func pool(t testing.TB, scale float64) *sim.World {
	t.Helper()
	w := sim.New(float64(cols)/scale, float64(rows*2)/scale, 1)
	w.Populate(sim.ScenePool)
	return w
}

func isBraille(r rune) bool { return r >= 0x2800 && r <= 0x28ff }

// lines renders f and returns its lines with escape sequences removed.
func lines(t *testing.T, r *Renderer, f Frame) []string {
	t.Helper()
	out := r.Render(f)
	ls := strings.Split(out, "\n")
	if len(ls) != f.Rows {
		t.Fatalf("got %d lines, want %d", len(ls), f.Rows)
	}
	for i, l := range ls {
		if w := ansi.StringWidth(l); w != f.Cols {
			t.Fatalf("line %d is %d cells wide, want %d", i, w, f.Cols)
		}
		if !strings.HasSuffix(l, "\x1b[m") {
			t.Fatalf("line %d doesn't end by resetting its style: %q", i, l[max(0, len(l)-12):])
		}
		ls[i] = ansi.Strip(l)
	}
	return ls
}

func TestEveryModeAndThemeFillsTheFrame(t *testing.T) {
	w := pool(t, 3)
	r := New()
	for _, theme := range Themes {
		for _, mode := range Modes {
			t.Run(theme.Name+"/"+mode.String(), func(t *testing.T) {
				ring := Ring{Visible: true, X: 40, Y: 20, Radius: 9, Style: RingPull}
				lines(t, r, Frame{World: w, Scale: 3, Cols: cols, Rows: rows, Mode: mode, Theme: theme, Ring: ring})
			})
		}
	}
}

func TestEmptyTankIsBackground(t *testing.T) {
	w := sim.New(20, 10, 1)
	for _, mode := range Modes {
		for i, l := range lines(t, New(), Frame{World: w, Scale: 4, Cols: cols, Rows: rows, Mode: mode, Theme: Themes[0]}) {
			if strings.TrimSpace(l) != "" {
				t.Fatalf("%v: line %d of an empty tank is %q, want only spaces", mode, i, l)
			}
		}
	}
}

func TestLiquidIsDrawnWhereParticlesAre(t *testing.T) {
	ls := lines(t, New(), Frame{World: pool(t, 3), Scale: 3, Cols: cols, Rows: rows, Mode: ModeLiquid, Theme: Themes[0]})
	// The pool fills the bottom 45% of the tank. Its interior is solid color,
	// drawn as spaces, so check the surface rows for half blocks instead.
	if top := strings.Join(ls[:rows/3], ""); strings.TrimSpace(top) != "" {
		t.Errorf("the top third of the tank should be empty, got %q", top)
	}
	surface := strings.Join(ls[rows/2-2:rows/2+2], "")
	if !strings.Contains(surface, "▀") {
		t.Errorf("the rows around the pool's surface have no half blocks: %q", surface)
	}
}

func TestLiquidColorsChangeWithDepth(t *testing.T) {
	r := New()
	out := r.Render(Frame{World: pool(t, 3), Scale: 3, Cols: cols, Rows: rows, Mode: ModeLiquid, Theme: Themes[0]})
	ls := strings.Split(out, "\n")
	near, deep := ls[rows/2+1], ls[rows-2]
	if near == deep {
		t.Error("liquid just below the surface is drawn like liquid at the bottom; want it to darken with depth")
	}
}

func TestRingIsBraille(t *testing.T) {
	r := New()
	w := sim.New(20, 10, 1)
	ring := Ring{Visible: true, X: 40, Y: 24, Radius: 8, Style: RingPush}
	ls := lines(t, r, Frame{World: w, Scale: 4, Cols: cols, Rows: rows, Mode: ModeLiquid, Theme: Themes[0], Ring: ring})
	var dots int
	for y, l := range ls {
		for x, c := range []rune(l) {
			if !isBraille(c) {
				continue
			}
			dots++
			// The ring spans 8 pixels around (40, 24), which is 8 cells
			// across and 4 rows down from row 12.
			if x < 31 || x > 49 || y < 7 || y > 17 {
				t.Errorf("ring dot at cell (%d, %d), outside the ring's bounds", x, y)
			}
		}
	}
	if dots < 20 {
		t.Errorf("ring has %d braille cells, want a full circle", dots)
	}

	ring.Visible = false
	for _, l := range lines(t, r, Frame{World: w, Scale: 4, Cols: cols, Rows: rows, Mode: ModeLiquid, Theme: Themes[0], Ring: ring}) {
		if strings.ContainsFunc(l, isBraille) {
			t.Fatalf("hidden ring still drew braille: %q", l)
		}
	}
}

func TestParticlesModeDrawsDots(t *testing.T) {
	ls := lines(t, New(), Frame{World: pool(t, 3), Scale: 3, Cols: cols, Rows: rows, Mode: ModeParticles, Theme: Themes[0]})
	if !strings.ContainsFunc(ls[rows-1], isBraille) {
		t.Errorf("bottom row has no particle dots: %q", ls[rows-1])
	}
	if strings.ContainsFunc(ls[0], isBraille) {
		t.Errorf("top row has particle dots above the pool: %q", ls[0])
	}
}

func TestTwoToneThemeBlendsDye(t *testing.T) {
	ink := ThemeNamed("ink")
	if ink == nil {
		t.Fatal("no ink theme")
	}
	if got := newPalette(ink).dyeLevels; got < 2 {
		t.Errorf("ink theme has %d dye levels, want at least 2", got)
	}
	if got := newPalette(Themes[0]).dyeLevels; got != 1 {
		t.Errorf("%s theme has %d dye levels, want 1", Themes[0].Name, got)
	}

	// The pool's left half has dye 0 and its right half dye 1, so with a
	// two-tone theme the two halves of the bottom row use different colors.
	out := New().Render(Frame{World: pool(t, 3), Scale: 3, Cols: cols, Rows: rows, Mode: ModeLiquid, Theme: ink})
	bottom := strings.Split(out, "\n")[rows-1]
	half := len(bottom) / 2
	if left, right := sgrSet(bottom[:half]), sgrSet(bottom[half:]); equalSets(left, right) {
		t.Errorf("both halves of the bottom row use the same colors %v", left)
	}
}

func sgrSet(s string) map[string]bool {
	set := map[string]bool{}
	for _, part := range strings.Split(s, "\x1b[")[1:] {
		if i := strings.IndexByte(part, 'm'); i > 0 {
			set[part[:i]] = true
		}
	}
	return set
}

func equalSets(a, b map[string]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}

func TestThemeNamed(t *testing.T) {
	for _, theme := range Themes {
		if got := ThemeNamed(theme.Name); got != theme {
			t.Errorf("ThemeNamed(%q) = %v, want %v", theme.Name, got, theme)
		}
	}
	if got := ThemeNamed("plaid"); got != nil {
		t.Errorf("ThemeNamed(%q) = %v, want nil", "plaid", got)
	}
}

func BenchmarkRender(b *testing.B) {
	w := pool(b, 3)
	for range 120 {
		w.Step(sim.StepDuration)
	}
	r := New()
	ring := Ring{Visible: true, X: 40, Y: 20, Radius: 9, Style: RingPush}
	for _, mode := range Modes {
		b.Run(mode.String(), func(b *testing.B) {
			for b.Loop() {
				r.Render(Frame{World: w, Scale: 3, Cols: 160, Rows: 48, Mode: mode, Theme: Themes[0], Ring: ring})
			}
		})
	}
}

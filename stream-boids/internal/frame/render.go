package frame

import (
	"fmt"
	"image"
	"math"

	"github.com/imjasonh/playground/stream-boids/internal/flock"
	"github.com/imjasonh/playground/stream-boids/internal/par"
)

// Scene is what one frame shows.
type Scene struct {
	Flock *flock.Flock
	// Labels names the first len(Labels) boids, which are channel members
	// and draw in gold.
	Labels []string
	HUD    HUD
	// Banner is the Super Chat being thanked, if any.
	Banner *Banner
	// HueShift rotates every boid's color.
	HueShift uint8
}

// HUD is the overlay in the top left corner.
type HUD struct {
	Viewers      int
	ViewersKnown bool
	Members      int
}

// Banner thanks one viewer, as "<Name> <Text>".
type Banner struct {
	Name string
	// Text follows the name, such as "sent $5.00".
	Text string
	// Tier is the Super Chat tier that colors the banner. Zero draws a
	// membership banner in gold.
	Tier int
}

var (
	gold      = RGB(255, 196, 40)
	labelInk  = RGB(255, 236, 170)
	white     = RGB(245, 245, 250)
	shadowInk = YUV{16, 128, 128}
)

// tierColors are the Super Chat tier colors, lowest tier first.
var tierColors = []YUV{
	RGB(30, 136, 229),
	RGB(0, 229, 255),
	RGB(29, 233, 182),
	RGB(255, 202, 40),
	RGB(245, 124, 0),
	RGB(233, 30, 99),
	RGB(230, 33, 23),
}

// TierColor returns the color of a Super Chat tier, counting from 1.
func TierColor(tier int) YUV {
	return tierColors[min(max(tier, 1), len(tierColors))-1]
}

// bandHeight is the number of rows one worker draws at a time. It is even
// so that every chroma row belongs to one band.
const bandHeight = 24

// Renderer draws scenes. It keeps the boids' fading trails between frames,
// so frames must be rendered in order. A Renderer is not safe for
// concurrent use.
type Renderer struct {
	w, h    int
	workers int
	scale   float64
	trail   *Frame
	bg      *Frame
	palette [256]YUV

	big, small, label *typeface

	// Per-frame scratch space.
	bandH      int
	bands      int
	bandOf     []int32
	color      []uint8
	bandStart  []int32
	bandOrder  []int32
	sprites    []sprite
	spriteBand [][]int32
}

// sprite is an overlay drawn on the output frame after the trail is
// copied, so it leaves no trail. A sprite with a nil mask dims its
// rectangle instead.
type sprite struct {
	mask *image.Alpha
	// at is the mask's top left corner and r is the part of the sprite
	// inside the frame.
	at  image.Point
	r   image.Rectangle
	ink YUV
}

// NewRenderer returns a renderer for w by h frames that uses workers
// goroutines.
func NewRenderer(w, h, workers int) (*Renderer, error) {
	trail, err := New(w, h)
	if err != nil {
		return nil, err
	}
	bg, err := New(w, h)
	if err != nil {
		return nil, err
	}
	workers = max(workers, 1)
	r := &Renderer{w: w, h: h, workers: workers, scale: float64(h) / 1080, trail: trail, bg: bg}
	if r.big, r.small, r.label, err = newTypefaces(r.scale); err != nil {
		return nil, err
	}
	for i := range r.palette {
		r.palette[i] = HSV(float64(i)/256, 0.62, 1)
	}
	// A dark gradient from navy at the top to plum at the bottom. Boid
	// trails fade toward it.
	for y := range h {
		t := float64(y) / float64(h-1)
		c := RGB(uint8(5+9*t), uint8(9-3*t), uint8(26+6*t))
		fill(bg.Y[y*w:(y+1)*w], c.Y)
		if y%2 == 0 {
			cw := w / 2
			fill(bg.U[(y/2)*cw:(y/2+1)*cw], c.U)
			fill(bg.V[(y/2)*cw:(y/2+1)*cw], c.V)
		}
	}
	copy(trail.buf, bg.buf)
	// The band height doesn't depend on the number of workers, so neither
	// does the order overlapping boids are drawn in. At 1080p this gives 45
	// bands, enough to balance the bands under a dense clump.
	r.bandH = bandHeight
	r.bands = (h + r.bandH - 1) / r.bandH
	r.bandStart = make([]int32, r.bands+1)
	r.spriteBand = make([][]int32, r.bands)
	return r, nil
}

// boidSize returns the side of a boid's square in pixels. Small flocks get
// larger boids so a stream with a handful of viewers still reads.
func (r *Renderer) boidSize(n int) int {
	var s int
	switch {
	case n <= 50:
		s = 7
	case n <= 500:
		s = 5
	case n <= 5000:
		s = 3
	default:
		s = 2
	}
	return max(int(math.Round(float64(s)*r.scale)), 1)
}

// Render draws sc into out. out must be the renderer's size.
func (r *Renderer) Render(sc *Scene, out *Frame) error {
	if out.W != r.w || out.H != r.h {
		return fmt.Errorf("output frame is %dx%d, want %dx%d", out.W, out.H, r.w, r.h)
	}
	fl := sc.Flock
	n := fl.Len()
	size := r.boidSize(n)
	r.bucket(fl, sc.HueShift)
	r.buildSprites(sc, size)

	par.For(r.bands, r.workers, func(lo, hi int) {
		for b := lo; b < hi; b++ {
			r.drawBand(b, fl, len(sc.Labels), size, out)
		}
	})
	return nil
}

// bucket sorts boids by the band their center falls in and picks each
// boid's color from its heading.
func (r *Renderer) bucket(fl *flock.Flock, shift uint8) {
	n := fl.Len()
	r.bandOf = grow(r.bandOf, n)
	r.color = grow(r.color, n)
	r.bandOrder = grow(r.bandOrder, n)
	par.For(n, r.workers, func(lo, hi int) {
		for i := lo; i < hi; i++ {
			r.bandOf[i] = int32(min(int(fl.Y[i])/r.bandH, r.bands-1))
			a := math.Atan2(float64(fl.VY[i]), float64(fl.VX[i]))
			r.color[i] = uint8(int((a/(2*math.Pi)+1)*256)) + shift
		}
	})
	clear(r.bandStart)
	for i := range n {
		r.bandStart[r.bandOf[i]+1]++
	}
	for b := 1; b <= r.bands; b++ {
		r.bandStart[b] += r.bandStart[b-1]
	}
	next := make([]int32, r.bands)
	copy(next, r.bandStart[:r.bands])
	for i := range n {
		b := r.bandOf[i]
		r.bandOrder[next[b]] = int32(i)
		next[b]++
	}
}

// buildSprites lays out the labels, HUD, and banner, and files each sprite
// under every band it overlaps.
func (r *Renderer) buildSprites(sc *Scene, size int) {
	r.sprites = r.sprites[:0]
	for b := range r.spriteBand {
		r.spriteBand[b] = r.spriteBand[b][:0]
	}
	s := func(v float64) int { return int(math.Round(v * r.scale)) }
	fl := sc.Flock

	for i, name := range sc.Labels {
		if i >= fl.Len() {
			break
		}
		m := r.label.mask(r.label.cleanName(name))
		if m.Rect.Empty() {
			continue
		}
		x := int(fl.X[i]) - m.Rect.Dx()/2
		y := int(fl.Y[i]) - size - s(8) - m.Rect.Dy()
		lp := s(4)
		r.dim(image.Rect(x-lp, y-lp, x+m.Rect.Dx()+lp, y+m.Rect.Dy()+lp))
		r.text(m, x, y, labelInk)
	}

	pad := s(18)
	x0, y0 := s(36), s(36)
	viewers := "-- viewers"
	if sc.HUD.ViewersKnown {
		viewers = plural(sc.HUD.Viewers, "viewer", "viewers")
	}
	vm := r.big.mask(viewers)
	mm := r.small.mask(plural(sc.HUD.Members, "member watching", "members watching"))
	gap := s(12)
	bw := max(vm.Rect.Dx(), mm.Rect.Dx()) + 2*pad
	bh := vm.Rect.Dy() + gap + mm.Rect.Dy() + 2*pad
	r.dim(image.Rect(x0, y0, x0+bw, y0+bh))
	r.text(vm, x0+pad, y0+pad, white)
	r.text(mm, x0+pad, y0+pad+vm.Rect.Dy()+gap, gold)

	if bn := sc.Banner; bn != nil {
		m := r.small.mask(r.small.cleanName(bn.Name) + " " + bn.Text)
		bw := m.Rect.Dx() + 2*pad
		bh := m.Rect.Dy() + 2*pad
		bx := (r.w - bw) / 2
		by := r.h - s(72) - bh
		r.dim(image.Rect(bx, by, bx+bw, by+bh))
		bar := s(6)
		ink := gold
		if bn.Tier > 0 {
			ink = TierColor(bn.Tier)
		}
		r.add(sprite{r: image.Rect(bx, by+bh-bar, bx+bw, by+bh), mask: solid, ink: ink})
		r.text(m, bx+pad, by+pad, ink)
	}
}

// solid marks a sprite that fills its rectangle with its ink.
var solid = image.NewAlpha(image.Rect(0, 0, 1, 1))

func plural(n int, one, many string) string {
	if n == 1 {
		return "1 " + one
	}
	return thousands(n) + " " + many
}

func (r *Renderer) text(m *image.Alpha, x, y int, ink YUV) {
	if m.Rect.Empty() {
		return
	}
	off := max(int(math.Round(2*r.scale)), 1)
	for _, sp := range []sprite{
		{mask: m, at: image.Pt(x+off, y+off), ink: shadowInk},
		{mask: m, at: image.Pt(x, y), ink: ink},
	} {
		sp.r = m.Rect.Add(sp.at)
		r.add(sp)
	}
}

func (r *Renderer) dim(rect image.Rectangle) {
	r.add(sprite{r: rect})
}

func (r *Renderer) add(sp sprite) {
	sp.r = sp.r.Intersect(image.Rect(0, 0, r.w, r.h))
	if sp.r.Empty() {
		return
	}
	idx := int32(len(r.sprites))
	r.sprites = append(r.sprites, sp)
	for b := sp.r.Min.Y / r.bandH; b <= (sp.r.Max.Y-1)/r.bandH && b < r.bands; b++ {
		r.spriteBand[b] = append(r.spriteBand[b], idx)
	}
}

// drawBand fades the trail rows of band b, draws the boids that touch
// them, copies the rows to out, and draws the band's part of each sprite.
func (r *Renderer) drawBand(b int, fl *flock.Flock, members, size int, out *Frame) {
	w, cw := r.w, r.w/2
	y0 := b * r.bandH
	y1 := min(y0+r.bandH, r.h)
	t, bg := r.trail, r.bg
	fade(t.Y[y0*w:y1*w], bg.Y[y0*w:y1*w])
	fade(t.U[y0/2*cw:y1/2*cw], bg.U[y0/2*cw:y1/2*cw])
	fade(t.V[y0/2*cw:y1/2*cw], bg.V[y0/2*cw:y1/2*cw])

	// A boid can reach into the bands next to its own.
	reach := (size + r.bandH - 1) / r.bandH
	for nb := max(b-reach, 0); nb <= min(b+reach, r.bands-1); nb++ {
		for k := r.bandStart[nb]; k < r.bandStart[nb+1]; k++ {
			if i := r.bandOrder[k]; int(i) >= members {
				r.dot(fl.X[i], fl.Y[i], size, r.palette[r.color[i]], y0, y1)
			}
		}
	}
	// Members draw last so viewers never cover them.
	gsize := size + 2*max(int(math.Round(r.scale)), 1)
	for i := range min(members, fl.Len()) {
		r.dot(fl.X[i], fl.Y[i], gsize, gold, y0, y1)
	}

	copy(out.Y[y0*w:y1*w], t.Y[y0*w:y1*w])
	copy(out.U[y0/2*cw:y1/2*cw], t.U[y0/2*cw:y1/2*cw])
	copy(out.V[y0/2*cw:y1/2*cw], t.V[y0/2*cw:y1/2*cw])

	for _, idx := range r.spriteBand[b] {
		r.blit(&r.sprites[idx], out, y0, y1)
	}
}

// dot draws a size by size square centered on (x, y) into the trail,
// clipped to rows [y0, y1).
func (r *Renderer) dot(x, y float32, size int, c YUV, y0, y1 int) {
	px := int(x) - size/2
	py := int(y) - size/2
	xa, xb := max(px, 0), min(px+size, r.w)
	ya, yb := max(py, y0), min(py+size, y1)
	if xa >= xb || ya >= yb {
		return
	}
	t := r.trail
	for yy := ya; yy < yb; yy++ {
		row := t.Y[yy*r.w:]
		for xx := xa; xx < xb; xx++ {
			row[xx] = c.Y
		}
	}
	cw := r.w / 2
	for cy := ya / 2; cy <= (yb-1)/2; cy++ {
		// Only the band that owns a chroma row writes it.
		if cy*2 < y0 || cy*2 >= y1 {
			continue
		}
		for cx := xa / 2; cx <= (xb-1)/2; cx++ {
			t.U[cy*cw+cx] = c.U
			t.V[cy*cw+cx] = c.V
		}
	}
}

// blit draws the part of sp in rows [y0, y1) onto out.
func (r *Renderer) blit(sp *sprite, out *Frame, y0, y1 int) {
	ya, yb := max(sp.r.Min.Y, y0), min(sp.r.Max.Y, y1)
	xa, xb := sp.r.Min.X, sp.r.Max.X
	w, cw := r.w, r.w/2
	if sp.mask == nil {
		for y := ya; y < yb; y++ {
			row := out.Y[y*w:]
			for x := xa; x < xb; x++ {
				row[x] = byte(int(row[x])*3/8 + 10)
			}
			if y%2 == 0 {
				for x := xa / 2; x < (xb+1)/2; x++ {
					u, v := &out.U[y/2*cw+x], &out.V[y/2*cw+x]
					*u = byte((int(*u) + 3*128) / 4)
					*v = byte((int(*v) + 3*128) / 4)
				}
			}
		}
		return
	}
	if sp.mask == solid {
		for y := ya; y < yb; y++ {
			row := out.Y[y*w:]
			for x := xa; x < xb; x++ {
				row[x] = sp.ink.Y
			}
			if y%2 == 0 {
				for x := xa / 2; x < (xb+1)/2; x++ {
					out.U[y/2*cw+x] = sp.ink.U
					out.V[y/2*cw+x] = sp.ink.V
				}
			}
		}
		return
	}
	m := sp.mask
	ox, oy := sp.at.X, sp.at.Y
	for y := ya; y < yb; y++ {
		row := out.Y[y*w:]
		mrow := m.Pix[(y-oy)*m.Stride:]
		for x := xa; x < xb; x++ {
			a := int(mrow[x-ox])
			if a == 0 {
				continue
			}
			row[x] = byte(int(row[x]) + (int(sp.ink.Y)-int(row[x]))*a/255)
			if x%2 == 0 && y%2 == 0 {
				u, v := &out.U[y/2*cw+x/2], &out.V[y/2*cw+x/2]
				*u = byte(int(*u) + (int(sp.ink.U)-int(*u))*a/255)
				*v = byte(int(*v) + (int(sp.ink.V)-int(*v))*a/255)
			}
		}
	}
}

func grow[T any](s []T, n int) []T {
	if cap(s) < n {
		return make([]T, n)
	}
	return s[:n]
}

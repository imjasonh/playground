// Package render draws a sim.World as styled terminal text.
//
// The liquid and heat modes treat each terminal cell as two square pixels
// stacked vertically and draw them with the upper half block character, using
// the foreground color for the top pixel and the background color for the
// bottom one. The particles mode draws each particle as one braille dot, which
// gives a 2×4 dot grid per cell. The brush outline is always drawn with
// braille dots so it stays thin over the liquid.
package render

import (
	"math"
	"unicode/utf8"

	"github.com/imjasonh/playground/liquid/internal/sim"
)

// Mode selects how the liquid is drawn.
type Mode int

// Render modes.
const (
	// ModeLiquid shades the liquid by depth below its surface and whitens it
	// where it moves fast.
	ModeLiquid Mode = iota
	// ModeParticles draws every particle as a braille dot colored by speed.
	ModeParticles
	// ModeHeat colors the liquid by speed.
	ModeHeat
)

// Modes lists every mode in the order the interface cycles through them.
var Modes = []Mode{ModeLiquid, ModeParticles, ModeHeat}

// String returns the mode's display name.
func (m Mode) String() string {
	switch m {
	case ModeParticles:
		return "particles"
	case ModeHeat:
		return "heat"
	default:
		return "liquid"
	}
}

// Ring is the brush outline.
type Ring struct {
	Visible bool
	// X and Y are the center of the ring in pixels, where a pixel is one cell
	// wide and half a cell tall.
	X, Y float64
	// Radius is the radius in pixels.
	Radius float64
	// Style is one of the Ring constants, such as RingPush.
	Style int
}

// Frame describes one picture of the tank.
type Frame struct {
	World *sim.World
	// Scale is the number of pixels per h, the simulation's unit of length.
	Scale float64
	// Cols and Rows are the size of the picture in terminal cells.
	Cols, Rows int
	Mode       Mode
	Theme      *Theme
	Ring       Ring
}

// Renderer turns frames into strings. It keeps its buffers between frames, so
// reuse one Renderer rather than creating one per frame. A Renderer isn't safe
// for concurrent use.
type Renderer struct {
	cols, rows int
	pw, ph     int // Size in pixels.

	dens, vx, vy, dye []float32 // Splatted fields, one entry per pixel.
	pix               []uint16  // Palette index of each pixel.
	ring              []uint8   // Braille bits of the ring, one entry per cell.
	dots              []uint8   // Braille bits of the particles, one entry per cell.
	dotSpeed          []float32 // Fastest particle in each cell.
	depth             []uint8   // Depth level by run of liquid pixels; see resize.

	theme *Theme
	pal   *palette
	out   []byte
}

// New returns a Renderer.
func New() *Renderer { return &Renderer{} }

// Tuning for the liquid mode.
const (
	// splatRadius is the reach of each particle's contribution to the density
	// field, in h.
	splatRadius = 0.85
	// bodyLevel and sprayLevel are density thresholds, as fractions of the
	// density inside resting liquid. Pixels above bodyLevel are liquid; pixels
	// between the two are translucent spray, which keeps lone droplets visible.
	bodyLevel  = 0.42
	sprayLevel = 0.11
	// foamSpeed is the speed, in h/s, at which liquid starts to whiten.
	foamSpeed = 11.0
	// heatSpeed is the speed, in h/s, at the hot end of the heat gradient.
	heatSpeed = 32.0
	// dotSpeedMax is the speed, in h/s, at the bright end of the particle
	// colors.
	dotSpeedMax = 24.0
)

// restDensity is the splatted density inside resting liquid. Particles sit on
// a lattice with sim.Spacing between them, and each one adds a kernel whose
// integral is π·R²/3, so the density doesn't depend on the scale.
var restDensity = math.Pi * splatRadius * splatRadius / (3 * sim.Spacing * sim.Spacing * math.Sqrt(3) / 2)

var brailleBit = [4][2]uint8{{0x01, 0x08}, {0x02, 0x10}, {0x04, 0x20}, {0x40, 0x80}}

// Render returns the frame as Rows lines of Cols cells each, separated by
// newlines. Every line ends by resetting its style.
func (r *Renderer) Render(f Frame) string {
	if f.Cols <= 0 || f.Rows <= 0 {
		return ""
	}
	r.resize(f.Cols, f.Rows)
	if f.Theme != r.theme || r.pal == nil {
		r.theme = f.Theme
		r.pal = newPalette(f.Theme)
	}
	r.traceRing(f.Ring)

	switch f.Mode {
	case ModeParticles:
		r.scatterDots(f.World, f.Scale)
		r.encodeDots(f.Ring.Style)
	case ModeHeat:
		r.splat(f.World, f.Scale)
		r.shadeHeat()
		r.encodeBlocks(f.Ring.Style)
	default:
		r.splat(f.World, f.Scale)
		r.shadeLiquid()
		r.encodeBlocks(f.Ring.Style)
	}
	return string(r.out)
}

func (r *Renderer) resize(cols, rows int) {
	if cols == r.cols && rows == r.rows {
		return
	}
	r.cols, r.rows = cols, rows
	r.pw, r.ph = cols, rows*2
	n := r.pw * r.ph
	r.dens = make([]float32, n)
	r.vx = make([]float32, n)
	r.vy = make([]float32, n)
	r.dye = make([]float32, n)
	r.pix = make([]uint16, n)
	r.ring = make([]uint8, cols*rows)
	r.dots = make([]uint8, cols*rows)
	r.dotSpeed = make([]float32, cols*rows)

	// depth[run] is the depth level of a pixel with run-1 liquid pixels above
	// it. The top pixel gets level 0, the surface highlight.
	r.depth = make([]uint8, r.ph+1)
	scale := math.Max(2.5, float64(r.ph)/7)
	for run := 2; run <= r.ph; run++ {
		t := 1 - math.Exp(-float64(run-1)/scale)
		r.depth[run] = uint8(min(depthLevels-1, 1+int(t*float64(depthLevels-1))))
	}
}

// splat adds each particle's kernel to the density, velocity, and dye fields.
// Velocity is splatted as a vector so that particles trembling in random
// directions cancel out and only flowing liquid reads as fast.
func (r *Renderer) splat(w *sim.World, scale float64) {
	clear(r.dens)
	clear(r.vx)
	clear(r.vy)
	clear(r.dye)
	if w == nil {
		return
	}
	radius := splatRadius * scale
	r2 := radius * radius
	inv := 1 / r2
	for i := range w.X {
		px, py := w.X[i]*scale, w.Y[i]*scale
		vx, vy := float32(w.VX[i]), float32(w.VY[i])
		dye := w.Dye[i]
		x0, x1 := max(int(px-radius), 0), min(int(px+radius), r.pw-1)
		y0, y1 := max(int(py-radius), 0), min(int(py+radius), r.ph-1)
		for y := y0; y <= y1; y++ {
			dy := float64(y) + 0.5 - py
			dy2 := dy * dy
			if dy2 >= r2 {
				continue
			}
			row := y * r.pw
			for x := x0; x <= x1; x++ {
				dx := float64(x) + 0.5 - px
				q := (dx*dx + dy2) * inv
				if q >= 1 {
					continue
				}
				k := float32((1 - q) * (1 - q))
				r.dens[row+x] += k
				r.vx[row+x] += k * vx
				r.vy[row+x] += k * vy
				r.dye[row+x] += k * dye
			}
		}
	}
}

// shadeLiquid picks a color for each pixel from the splatted fields. Liquid
// darkens with depth, measured as the number of liquid pixels above it in its
// column, so light appears to come from above.
func (r *Renderer) shadeLiquid() {
	p := r.pal
	body := float32(bodyLevel * restDensity)
	spray := float32(sprayLevel * restDensity)
	levels := r.depth
	for x := range r.pw {
		run := 0
		for y := range r.ph {
			k := y*r.pw + x
			d := r.dens[k]
			if d < spray {
				r.pix[k] = p.background(y, r.ph)
				run = 0
				continue
			}
			speed := r.flow(k)
			dye := r.dyeLevel(r.dye[k] / d)
			if d < body {
				r.pix[k] = p.spray(dye, speed > foamSpeed)
				run = 0
				continue
			}
			run++
			r.pix[k] = p.liquid(dye, int(levels[run]), foamLevel(speed, run))
		}
	}
}

// flow returns the speed of the splatted velocity at pixel k, in h/s.
func (r *Renderer) flow(k int) float32 {
	d := r.dens[k]
	return float32(math.Hypot(float64(r.vx[k]/d), float64(r.vy[k]/d)))
}

func (r *Renderer) dyeLevel(dye float32) int {
	n := r.pal.dyeLevels
	if n == 1 {
		return 0
	}
	return min(max(int(dye*float32(n-1)+0.5), 0), n-1)
}

// foamLevel whitens fast liquid. Foam forms where breaking waves trap air, so
// it forms sooner near the surface and rarely deep down.
func foamLevel(speed float32, run int) int {
	s := float64(speed)
	switch {
	case run <= 2:
		s *= 1.3
	case run > 8:
		s *= 0.7
	}
	if s < foamSpeed {
		return 0
	}
	return min(foamLevels-1, 1+int((s-foamSpeed)/7))
}

func (r *Renderer) shadeHeat() {
	p := r.pal
	spray := float32(sprayLevel * restDensity)
	for y := range r.ph {
		for x := range r.pw {
			k := y*r.pw + x
			d := r.dens[k]
			if d < spray {
				r.pix[k] = p.background(y, r.ph)
				continue
			}
			t := float64(r.flow(k)) / heatSpeed
			r.pix[k] = p.heat(min(heatLevels-1, int(math.Sqrt(t)*heatLevels)))
		}
	}
}

// scatterDots marks one braille dot per particle.
func (r *Renderer) scatterDots(w *sim.World, scale float64) {
	clear(r.dots)
	clear(r.dotSpeed)
	if w == nil {
		return
	}
	dw, dh := r.cols*2, r.rows*4
	for i := range w.X {
		dx := int(w.X[i] * scale * 2)
		dy := int(w.Y[i] * scale * 2)
		if dx < 0 || dy < 0 || dx >= dw || dy >= dh {
			continue
		}
		c := (dy/4)*r.cols + dx/2
		r.dots[c] |= brailleBit[dy%4][dx%2]
		r.dotSpeed[c] = max(r.dotSpeed[c], float32(math.Hypot(w.VX[i], w.VY[i])))
	}
}

// traceRing marks the braille dots that the ring passes through.
func (r *Renderer) traceRing(ring Ring) {
	clear(r.ring)
	if !ring.Visible || ring.Radius <= 0 {
		return
	}
	const halfWidth = 0.3 // In pixels.
	dashed := ring.Style == RingIdle
	outer := ring.Radius + halfWidth
	// Dots are half a pixel wide and half a pixel tall.
	x0 := max(int((ring.X-outer)*2), 0)
	x1 := min(int((ring.X+outer)*2)+1, r.cols*2-1)
	y0 := max(int((ring.Y-outer)*2), 0)
	y1 := min(int((ring.Y+outer)*2)+1, r.rows*4-1)
	for dy := y0; dy <= y1; dy++ {
		py := (float64(dy)+0.5)/2 - ring.Y
		for dx := x0; dx <= x1; dx++ {
			px := (float64(dx)+0.5)/2 - ring.X
			d := math.Hypot(px, py)
			if math.Abs(d-ring.Radius) > halfWidth {
				continue
			}
			if dashed {
				arc := (math.Atan2(py, px) + math.Pi) * ring.Radius
				if int(arc/1.2)%2 != 0 {
					continue
				}
			}
			r.ring[(dy/4)*r.cols+dx/2] |= brailleBit[dy%4][dx%2]
		}
	}
}

// sgr tracks the colors in effect while encoding a line, so the encoder only
// emits escape sequences when a color changes.
type sgr struct {
	fg, bg int
}

func (r *Renderer) setColors(s *sgr, fg, bg int) {
	p := r.pal
	switch {
	case fg >= 0 && fg != s.fg && bg != s.bg:
		r.out = append(r.out, "\x1b["...)
		r.out = append(r.out, p.fg[fg]...)
		r.out = append(r.out, ';')
		r.out = append(r.out, p.bg[bg]...)
		r.out = append(r.out, 'm')
	case fg >= 0 && fg != s.fg:
		r.out = append(r.out, "\x1b["...)
		r.out = append(r.out, p.fg[fg]...)
		r.out = append(r.out, 'm')
	case bg != s.bg:
		r.out = append(r.out, "\x1b["...)
		r.out = append(r.out, p.bg[bg]...)
		r.out = append(r.out, 'm')
	}
	if fg >= 0 {
		s.fg = fg
	}
	s.bg = bg
}

// encodeBlocks writes the pixels as half blocks, with ring cells drawn as
// braille over the cell's color.
func (r *Renderer) encodeBlocks(ringStyle int) {
	r.out = r.out[:0]
	ringColor := int(r.pal.ring(ringStyle))
	for row := range r.rows {
		s := sgr{fg: -1, bg: -1}
		top := r.pix[2*row*r.pw : (2*row+1)*r.pw]
		bottom := r.pix[(2*row+1)*r.pw : (2*row+2)*r.pw]
		for col := range r.cols {
			t, b := top[col], bottom[col]
			if bits := r.ring[row*r.cols+col]; bits != 0 {
				bg := t
				if r.pal.isBackground(t) && !r.pal.isBackground(b) {
					bg = b
				}
				r.setColors(&s, ringColor, int(bg))
				r.out = utf8.AppendRune(r.out, 0x2800+rune(bits))
				continue
			}
			if t == b {
				r.setColors(&s, -1, int(b))
				r.out = append(r.out, ' ')
				continue
			}
			r.setColors(&s, int(t), int(b))
			r.out = append(r.out, "▀"...)
		}
		r.out = append(r.out, "\x1b[m"...)
		if row < r.rows-1 {
			r.out = append(r.out, '\n')
		}
	}
}

// encodeDots writes the particle and ring dots as braille.
func (r *Renderer) encodeDots(ringStyle int) {
	r.out = r.out[:0]
	p := r.pal
	ringColor := int(p.ring(ringStyle))
	for row := range r.rows {
		s := sgr{fg: -1, bg: -1}
		bg := int(p.background(row*2+1, r.ph))
		for col := range r.cols {
			c := row*r.cols + col
			ringBits, dotBits := r.ring[c], r.dots[c]
			switch {
			case ringBits != 0:
				r.setColors(&s, ringColor, bg)
				r.out = utf8.AppendRune(r.out, 0x2800+rune(ringBits|dotBits))
			case dotBits != 0:
				level := min(dotLevels-1, int(r.dotSpeed[c]/dotSpeedMax*dotLevels))
				r.setColors(&s, int(p.dot(level)), bg)
				r.out = utf8.AppendRune(r.out, 0x2800+rune(dotBits))
			default:
				r.setColors(&s, -1, bg)
				r.out = append(r.out, ' ')
			}
		}
		r.out = append(r.out, "\x1b[m"...)
		if row < r.rows-1 {
			r.out = append(r.out, '\n')
		}
	}
}

package render

import (
	"image/color"
	"math"
	"strconv"

	"charm.land/lipgloss/v2"
	"github.com/lucasb-eyer/go-colorful"
)

// Theme is a color scheme for the liquid and the interface around it.
type Theme struct {
	Name string
	// Accent colors the interface: the title, active buttons, and the border.
	Accent color.Color
	// BackgroundTop and BackgroundBottom are the empty tank, from top to
	// bottom.
	BackgroundTop, BackgroundBottom color.Color
	// Liquid holds the liquid's color stops from the surface to the depths.
	Liquid []color.Color
	// Mix, when set, makes the theme two-tone. Particles with a dye of 1 use
	// these stops instead of Liquid, and the renderer blends the two where the
	// liquids mix.
	Mix []color.Color
	// Foam is the color that fast-moving liquid turns toward.
	Foam color.Color
}

func hex(s string) color.Color { return lipgloss.Color(s) }

// Themes lists the built-in themes. The first is the default.
var Themes = []*Theme{
	{
		Name:             "ocean",
		Accent:           hex("#5fd7ff"),
		BackgroundTop:    hex("#03070f"),
		BackgroundBottom: hex("#0a1830"),
		Liquid:           []color.Color{hex("#b5f6ff"), hex("#2fb6f0"), hex("#1565c8"), hex("#0a2a6e")},
		Foam:             hex("#f4fdff"),
	},
	{
		Name:             "lava",
		Accent:           hex("#ff9248"),
		BackgroundTop:    hex("#0d0404"),
		BackgroundBottom: hex("#23090a"),
		Liquid:           []color.Color{hex("#fff3a3"), hex("#ffae33"), hex("#f0471b"), hex("#7a0d12")},
		Foam:             hex("#fffbe8"),
	},
	{
		Name:             "slime",
		Accent:           hex("#a6e85c"),
		BackgroundTop:    hex("#030a05"),
		BackgroundBottom: hex("#0b1d10"),
		Liquid:           []color.Color{hex("#efffa3"), hex("#9be342"), hex("#2f9e3c"), hex("#0d4a26")},
		Foam:             hex("#fbffe6"),
	},
	{
		Name:             "ink",
		Accent:           hex("#e08cff"),
		BackgroundTop:    hex("#07060d"),
		BackgroundBottom: hex("#161028"),
		Liquid:           []color.Color{hex("#a8faff"), hex("#28c4dc"), hex("#0f7f9e"), hex("#0a3a5c")},
		Mix:              []color.Color{hex("#ffc2f0"), hex("#ff5cc8"), hex("#c01c86"), hex("#5c0b45")},
		Foam:             hex("#ffffff"),
	},
	{
		Name:             "mercury",
		Accent:           hex("#c9d3df"),
		BackgroundTop:    hex("#060708"),
		BackgroundBottom: hex("#14181d"),
		Liquid:           []color.Color{hex("#ffffff"), hex("#c3ccd6"), hex("#6f7b89"), hex("#2b333d")},
		Foam:             hex("#ffffff"),
	},
}

// ThemeNamed returns the built-in theme with the given name, or nil.
func ThemeNamed(name string) *Theme {
	for _, t := range Themes {
		if t.Name == name {
			return t
		}
	}
	return nil
}

// Palette sizes. Depth level 0 is the surface highlight.
const (
	bgLevels    = 16
	depthLevels = 14
	foamLevels  = 4
	heatLevels  = 24
	dotLevels   = 8
)

// Ring styles for the brush outline.
const (
	RingIdle = iota
	RingPush
	RingPull
	RingAttract
	RingDisperse
	RingPour
	ringStyles
)

var ringColors = [ringStyles]color.Color{
	RingIdle:     hex("#8a93a6"),
	RingPush:     hex("#ff7a59"),
	RingPull:     hex("#6dffb0"),
	RingAttract:  hex("#7cc8ff"),
	RingDisperse: hex("#d79bff"),
	RingPour:     hex("#ffe27a"),
}

var heatStops = []color.Color{
	hex("#1b0c41"), hex("#4a0c6b"), hex("#781c6d"), hex("#a52c60"),
	hex("#cf4446"), hex("#ed6925"), hex("#fb9b06"), hex("#f7d13d"), hex("#fcffa4"),
}

// palette maps small integer indices to colors, with each color's SGR
// parameters precomputed so encoding a frame is mostly byte copying.
type palette struct {
	fg, bg [][]byte // "38;2;R;G;B" and "48;2;R;G;B" for each index.

	dyeLevels int
	bgBase    int
	liqBase   int
	sprayBase int
	heatBase  int
	dotBase   int
	ringBase  int
}

func newPalette(t *Theme) *palette {
	p := &palette{dyeLevels: 1}
	if len(t.Mix) > 0 {
		p.dyeLevels = 5
	}
	var colors []colorful.Color
	add := func(c colorful.Color) { colors = append(colors, c.Clamped()) }

	bgTop, bgBottom := toColorful(t.BackgroundTop), toColorful(t.BackgroundBottom)
	p.bgBase = len(colors)
	for i := range bgLevels {
		add(bgTop.BlendOkLab(bgBottom, float64(i)/float64(bgLevels-1)))
	}
	bgMid := bgTop.BlendOkLab(bgBottom, 0.6)

	primary := gradient(depthLevels, t.Liquid)
	secondary := primary
	if len(t.Mix) > 0 {
		secondary = gradient(depthLevels, t.Mix)
	}
	foam := toColorful(t.Foam)
	// Mixed liquid blends hue rather than mixing in a straight line, so
	// cyan and magenta meet in violet instead of gray.
	liquid := func(dye, depth int) colorful.Color {
		if p.dyeLevels == 1 {
			return primary[depth]
		}
		return blendHue(primary[depth], secondary[depth], float64(dye)/float64(p.dyeLevels-1))
	}

	p.liqBase = len(colors)
	for dye := range p.dyeLevels {
		for depth := range depthLevels {
			for f := range foamLevels {
				add(liquid(dye, depth).BlendOkLab(foam, float64(f)*0.2))
			}
		}
	}

	// Spray is thin liquid: lighter than the body but tinted by it, with a
	// little of the background showing through.
	p.sprayBase = len(colors)
	for dye := range p.dyeLevels {
		edge := liquid(dye, 0).BlendOkLab(liquid(dye, depthLevels/3), 0.45)
		add(edge.BlendOkLab(bgMid, 0.2))
		add(edge.BlendOkLab(foam, 0.5).BlendOkLab(bgMid, 0.1))
	}

	p.heatBase = len(colors)
	for _, c := range gradient(heatLevels, heatStops) {
		add(c)
	}

	p.dotBase = len(colors)
	for dye := range p.dyeLevels {
		slow, fast := liquid(dye, depthLevels/3), liquid(dye, 0)
		for level := range dotLevels {
			f := float64(level) / float64(dotLevels-1)
			if f < 0.6 {
				add(slow.BlendOkLab(fast, f/0.6))
			} else {
				add(fast.BlendOkLab(foam, (f-0.6)/0.4))
			}
		}
	}

	p.ringBase = len(colors)
	for _, c := range ringColors {
		add(toColorful(c))
	}

	p.fg = make([][]byte, len(colors))
	p.bg = make([][]byte, len(colors))
	for i, c := range colors {
		r, g, b := c.RGB255()
		p.fg[i] = sgrColor(38, r, g, b)
		p.bg[i] = sgrColor(48, r, g, b)
	}
	return p
}

// background returns the background color of pixel row y in a tank rows
// pixels tall. Both pixels of a cell share a color, so empty cells are spaces.
func (p *palette) background(y, rows int) uint16 {
	y &^= 1
	return uint16(p.bgBase + min(y*bgLevels/max(rows, 1), bgLevels-1))
}

func (p *palette) isBackground(i uint16) bool {
	return int(i) < p.bgBase+bgLevels
}

func (p *palette) liquid(dye, depth, foam int) uint16 {
	return uint16(p.liqBase + (dye*depthLevels+depth)*foamLevels + foam)
}

func (p *palette) spray(dye int, fast bool) uint16 {
	i := p.sprayBase + dye*2
	if fast {
		i++
	}
	return uint16(i)
}

func (p *palette) heat(level int) uint16 { return uint16(p.heatBase + level) }

func (p *palette) dot(dye, level int) uint16 { return uint16(p.dotBase + dye*dotLevels + level) }

func (p *palette) ring(style int) uint16 { return uint16(p.ringBase + style) }

// blendHue blends a toward b in OkLCh, taking the shorter way around the hue
// circle.
func blendHue(a, b colorful.Color, t float64) colorful.Color {
	l1, c1, h1 := a.OkLch()
	l2, c2, h2 := b.OkLch()
	dh := math.Mod(h2-h1+540, 360) - 180
	return colorful.OkLch(l1+(l2-l1)*t, c1+(c2-c1)*t, math.Mod(h1+dh*t+360, 360))
}

func toColorful(c color.Color) colorful.Color {
	cf, _ := colorful.MakeColor(c)
	return cf
}

// gradient blends stops into n colors with Lip Gloss's CIELAB blending.
func gradient(n int, stops []color.Color) []colorful.Color {
	out := make([]colorful.Color, 0, n)
	for _, c := range lipgloss.Blend1D(n, stops...) {
		out = append(out, toColorful(c))
	}
	return out
}

func sgrColor(kind int, r, g, b uint8) []byte {
	out := strconv.AppendInt(nil, int64(kind), 10)
	out = append(out, ";2;"...)
	out = strconv.AppendUint(out, uint64(r), 10)
	out = append(out, ';')
	out = strconv.AppendUint(out, uint64(g), 10)
	out = append(out, ';')
	out = strconv.AppendUint(out, uint64(b), 10)
	return out
}

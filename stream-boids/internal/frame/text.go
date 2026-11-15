package frame

import (
	"fmt"
	"image"
	"strings"
	"unicode"
	"unicode/utf8"

	"golang.org/x/image/font"
	"golang.org/x/image/font/gofont/gobold"
	"golang.org/x/image/font/gofont/gomedium"
	"golang.org/x/image/font/opentype"
	"golang.org/x/image/math/fixed"
)

// maxNameRunes is the longest viewer name drawn in full. Longer names end
// in an ellipsis.
const maxNameRunes = 24

// textCacheLimit bounds the number of cached masks. Names come from chat,
// so the set is unbounded; the cache starts over when it is full.
const textCacheLimit = 4096

// typeface renders strings into alpha masks and caches them. Font faces are
// not safe for concurrent use, so masks are only rendered by the goroutine
// that calls Render.
type typeface struct {
	face  font.Face
	cache map[string]*image.Alpha
}

func newTypeface(ttf []byte, size float64) (*typeface, error) {
	f, err := opentype.Parse(ttf)
	if err != nil {
		return nil, fmt.Errorf("parsing font: %w", err)
	}
	face, err := opentype.NewFace(f, &opentype.FaceOptions{Size: size, DPI: 72, Hinting: font.HintingFull})
	if err != nil {
		return nil, fmt.Errorf("creating face: %w", err)
	}
	return &typeface{face: face, cache: map[string]*image.Alpha{}}, nil
}

func newTypefaces(scale float64) (big, small, label *typeface, err error) {
	if big, err = newTypeface(gobold.TTF, 46*scale); err != nil {
		return nil, nil, nil, err
	}
	if small, err = newTypeface(gomedium.TTF, 30*scale); err != nil {
		return nil, nil, nil, err
	}
	if label, err = newTypeface(gomedium.TTF, 18*scale); err != nil {
		return nil, nil, nil, err
	}
	return big, small, label, nil
}

// mask returns s rendered as an alpha mask, tightly cropped to its ink.
func (t *typeface) mask(s string) *image.Alpha {
	if m, ok := t.cache[s]; ok {
		return m
	}
	if len(t.cache) >= textCacheLimit {
		clear(t.cache)
	}
	m := t.render(s)
	t.cache[s] = m
	return m
}

func (t *typeface) render(s string) *image.Alpha {
	d := &font.Drawer{Face: t.face}
	b, adv := d.BoundString(s)
	if adv == 0 {
		return image.NewAlpha(image.Rect(0, 0, 0, 0))
	}
	r := image.Rect(b.Min.X.Floor(), b.Min.Y.Floor(), b.Max.X.Ceil(), b.Max.Y.Ceil())
	m := image.NewAlpha(image.Rect(0, 0, r.Dx(), r.Dy()))
	d.Dst = m
	d.Src = image.Opaque
	d.Dot = fixed.P(-r.Min.X, -r.Min.Y)
	d.DrawString(s)
	return m
}

// cleanName makes a viewer's display name safe to draw: it drops control
// and formatting characters (including bidirectional overrides), replaces
// characters the face has no glyph for, collapses spaces, and shortens long
// names.
func (t *typeface) cleanName(s string) string {
	var out []rune
	space := false
	for _, r := range s {
		switch {
		case unicode.IsSpace(r):
			space = len(out) > 0
			continue
		case r == utf8.RuneError || unicode.IsControl(r) || unicode.Is(unicode.Cf, r):
			continue
		}
		if space {
			out = append(out, ' ')
			space = false
		}
		if _, ok := t.face.GlyphAdvance(r); !ok {
			r = '?'
		}
		out = append(out, r)
	}
	if len(out) > maxNameRunes {
		return strings.TrimRight(string(out[:maxNameRunes]), " ") + "…"
	}
	return string(out)
}

// thousands formats n with comma separators.
func thousands(n int) string {
	if n < 0 {
		return "-" + thousands(-n)
	}
	s := fmt.Sprint(n)
	var b strings.Builder
	for i, c := range s {
		if i > 0 && (len(s)-i)%3 == 0 {
			b.WriteByte(',')
		}
		b.WriteRune(c)
	}
	return b.String()
}

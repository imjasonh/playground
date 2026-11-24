// Package frame draws the stream's video frames in planar YUV 4:2:0, the
// format the encoder reads, so no frame is converted from RGB.
package frame

import (
	"encoding/binary"
	"fmt"
	"math"
)

// Frame is one picture in planar YUV 4:2:0 (yuv420p) with BT.709 limited
// range values. Y has one byte per pixel; U and V have one byte per 2x2
// block. The three planes share one buffer in Y, U, V order, which is the
// layout ffmpeg's rawvideo demuxer reads.
type Frame struct {
	W, H    int
	Y, U, V []byte
	buf     []byte
}

// New returns a black frame. w and h must be positive and even, because
// each chroma sample covers a 2x2 block.
func New(w, h int) (*Frame, error) {
	if w <= 0 || h <= 0 || w%2 != 0 || h%2 != 0 {
		return nil, fmt.Errorf("frame size %dx%d is not positive and even", w, h)
	}
	ys, cs := w*h, (w/2)*(h/2)
	buf := make([]byte, ys+2*cs)
	f := &Frame{W: w, H: h, buf: buf, Y: buf[:ys], U: buf[ys : ys+cs], V: buf[ys+cs:]}
	f.Fill(YUV{16, 128, 128})
	return f, nil
}

// Bytes returns the whole frame in yuv420p layout.
func (f *Frame) Bytes() []byte { return f.buf }

// Fill sets every pixel to c.
func (f *Frame) Fill(c YUV) {
	fill(f.Y, c.Y)
	fill(f.U, c.U)
	fill(f.V, c.V)
}

func fill(b []byte, v byte) {
	for i := range b {
		b[i] = v
	}
}

// YUV is a BT.709 limited range color.
type YUV struct{ Y, U, V byte }

// RGB converts 8-bit sRGB to BT.709 limited range YUV.
func RGB(r, g, b uint8) YUV {
	rf, gf, bf := float64(r)/255, float64(g)/255, float64(b)/255
	y := 0.2126*rf + 0.7152*gf + 0.0722*bf
	return YUV{
		Y: clamp8(16 + 219*y),
		U: clamp8(128 + 224*(bf-y)/1.8556),
		V: clamp8(128 + 224*(rf-y)/1.5748),
	}
}

// HSV converts hue (turns, [0, 1)), saturation, and value to YUV.
func HSV(h, s, v float64) YUV {
	h = (h - math.Floor(h)) * 6
	i := int(h)
	f := h - float64(i)
	p, q, t := v*(1-s), v*(1-s*f), v*(1-s*(1-f))
	var r, g, b float64
	switch i {
	case 0:
		r, g, b = v, t, p
	case 1:
		r, g, b = q, v, p
	case 2:
		r, g, b = p, v, t
	case 3:
		r, g, b = p, q, v
	case 4:
		r, g, b = t, p, v
	default:
		r, g, b = v, p, q
	}
	return RGB(uint8(r*255+0.5), uint8(g*255+0.5), uint8(b*255+0.5))
}

func clamp8(v float64) byte {
	return byte(min(max(math.Round(v), 0), 255))
}

// fade moves each byte of fb about 1/8 of the way toward the same byte of
// bg, eight bytes at a time, so trails fade into the background.
//
// Each byte becomes (f*224 + b*32) >> 8, plus 1 when f < b. Rounding down
// alone would leave a byte just below the background stuck there forever,
// which shows as dark lines where trails used to be. The words are split
// into even and odd bytes so each lane has 16 bits of room.
func fade(fb, bg []byte) {
	const (
		m = 0x00FF00FF00FF00FF
		h = 0x0100010001000100
		l = 0x0001000100010001
	)
	lane := func(f, b uint64) uint64 {
		v := ((f*224 + b*32) >> 8) & m
		// Bit 8 of each lane of (b + 256) - f - 1 is set when b > f.
		up := (((b | h) - f - l) >> 8) & l
		return v + up
	}
	i := 0
	for ; i+8 <= len(fb); i += 8 {
		a := binary.LittleEndian.Uint64(fb[i:])
		b := binary.LittleEndian.Uint64(bg[i:])
		e := lane(a&m, b&m)
		o := lane((a>>8)&m, (b>>8)&m)
		binary.LittleEndian.PutUint64(fb[i:], e|o<<8)
	}
	for ; i < len(fb); i++ {
		fb[i] = fadeByte(fb[i], bg[i])
	}
}

func fadeByte(f, b byte) byte {
	v := byte((int(f)*224 + int(b)*32) >> 8)
	if f < b {
		v++
	}
	return v
}

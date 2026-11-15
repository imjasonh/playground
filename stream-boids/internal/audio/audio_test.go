package audio

import (
	"bytes"
	"encoding/binary"
	"math"
	"testing"
)

const rate = 48000

func samples(buf []byte) []int16 {
	out := make([]int16, len(buf)/2)
	for i := range out {
		out[i] = int16(binary.LittleEndian.Uint16(buf[2*i:]))
	}
	return out
}

func rms(buf []byte) float64 {
	var sum float64
	s := samples(buf)
	for _, v := range s {
		sum += float64(v) * float64(v)
	}
	return math.Sqrt(sum / float64(len(s)))
}

func TestChunkingDoesNotChangeOutput(t *testing.T) {
	a, b := New(rate), New(rate)
	whole := make([]byte, 20*rate*BytesPerFrame)
	a.Bell(3)
	a.Fill(whole)
	b.Bell(3)
	var chunks bytes.Buffer
	chunk := make([]byte, 800*BytesPerFrame)
	for range 20 * 60 {
		b.Fill(chunk)
		chunks.Write(chunk)
	}
	if !bytes.Equal(whole, chunks.Bytes()) {
		t.Error("output depends on how Fill calls are sized")
	}
}

func TestPadIsQuietButAudible(t *testing.T) {
	s := New(rate)
	buf := make([]byte, 40*rate*BytesPerFrame)
	s.Fill(buf)
	if r := rms(buf); r < 500 || r > 8000 {
		t.Errorf("pad RMS = %.0f, want between 500 and 8000", r)
	}
}

func TestBurstDoesNotClip(t *testing.T) {
	s := New(rate)
	for range 100 {
		s.Bell(7)
		s.Chirp()
	}
	if len(s.voices) > maxVoices {
		t.Errorf("%d voices, want at most %d", len(s.voices), maxVoices)
	}
	buf := make([]byte, 2*rate*BytesPerFrame)
	s.Fill(buf)
	for i, v := range samples(buf) {
		if v >= 32000 || v <= -32000 {
			t.Fatalf("sample %d = %d, clipped", i, v)
		}
	}
}

func TestBellIsLouderThanPad(t *testing.T) {
	quiet, loud := New(rate), New(rate)
	loud.Bell(1)
	a := make([]byte, rate/2*BytesPerFrame)
	b := make([]byte, rate/2*BytesPerFrame)
	quiet.Fill(a)
	loud.Fill(b)
	if rq, rl := rms(a), rms(b); rl < 2*rq {
		t.Errorf("RMS with a bell = %.0f, without = %.0f; want at least double", rl, rq)
	}
}

func TestVoicesDieAway(t *testing.T) {
	s := New(rate)
	s.Bell(7)
	s.Chirp()
	buf := make([]byte, 10*rate*BytesPerFrame)
	s.Fill(buf)
	if len(s.voices) != 0 {
		t.Errorf("%d voices still ringing after 10s", len(s.voices))
	}
}

func BenchmarkFillOneVideoFrame(b *testing.B) {
	s := New(rate)
	buf := make([]byte, 800*BytesPerFrame)
	for b.Loop() {
		s.Fill(buf)
	}
}

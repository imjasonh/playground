// Package audio synthesizes the stream's soundtrack: a slow chord pad, a
// bell for each Super Chat, and a chirp when a member shows up.
//
// YouTube rejects or flags streams without an audio track, and a quiet pad
// is easier to leave running than silence.
package audio

import (
	"encoding/binary"
	"math"
)

// Channels is the number of interleaved channels Fill writes.
const Channels = 2

// BytesPerFrame is the size of one sample frame (one sample per channel)
// in s16le.
const BytesPerFrame = 2 * Channels

const tableSize = 4096

var sine = func() [tableSize + 1]float32 {
	var t [tableSize + 1]float32
	for i := range t {
		t[i] = float32(math.Sin(2 * math.Pi * float64(i) / tableSize))
	}
	return t
}()

// osc is a sine oscillator with a phase in turns.
type osc struct {
	phase, step float64
}

func (o *osc) next() float32 {
	p := o.phase * tableSize
	i := int(p)
	f := float32(p - float64(i))
	v := sine[i] + (sine[i+1]-sine[i])*f
	o.phase += o.step
	o.phase -= math.Floor(o.phase)
	return v
}

// chords are the pad's progression (A minor, F, C, G), as semitones from
// A2.
var chords = [][]int{
	{0, 7, 12, 15},
	{-4, 3, 8, 12},
	{3, 10, 15, 19},
	{-2, 5, 10, 14},
}

// chordSeconds is how long each chord of the pad lasts.
const chordSeconds = 8

type padNote struct {
	a, b       osc
	amp, level float32
	pan        float32
}

// voice is a note that rings once and dies away: a bell partial or a
// chirp.
type voice struct {
	osc
	// sweep multiplies step each sample, for a pitch glide.
	sweep       float64
	amp, decay  float32
	gain        float32
	left, right float32
}

// Synth generates the soundtrack. It is not safe for concurrent use; the
// render loop calls it once per video frame.
type Synth struct {
	rate   int
	sample uint64
	notes  []padNote
	// chordNotes lists the indexes in notes of each chord's notes.
	chordNotes [][]int
	chord      int
	voices     []voice
	smooth     float32
	lfo        osc
}

// New returns a synth that generates rate samples per second.
func New(rate int) *Synth {
	s := &Synth{rate: rate, chord: -1}
	// One-pole smoothing that moves about 63% of the way to a note's target
	// level in 1.5 seconds.
	s.smooth = float32(1 - math.Exp(-1/(1.5*float64(rate))))
	s.lfo.step = 0.07 / float64(rate)
	// Chords share notes, so each semitone gets one pair of oscillators.
	idx := map[int]int{}
	s.chordNotes = make([][]int, len(chords))
	for ci, c := range chords {
		for _, n := range c {
			i, ok := idx[n]
			if !ok {
				i = len(s.notes)
				idx[n] = i
				hz := 110 * math.Pow(2, float64(n)/12)
				s.notes = append(s.notes, padNote{
					a:   osc{step: hz / float64(rate)},
					b:   osc{step: hz * 1.003 / float64(rate), phase: 0.25},
					pan: float32(i%3-1) * 0.35,
				})
			}
			s.chordNotes[ci] = append(s.chordNotes[ci], i)
		}
	}
	return s
}

// Bell rings a bell for a Super Chat. Higher tiers ring lower, longer, and
// louder.
func (s *Synth) Bell(tier int) {
	tier = min(max(tier, 1), 7)
	hz := 1046.5 * math.Pow(2, -float64(tier-1)/6)
	seconds := 1.5 + 0.5*float64(tier)
	gain := 0.22 + 0.03*float32(tier)
	// Inharmonic partials make it sound struck rather than played.
	for i, ratio := range []float64{1, 2.76, 5.40, 8.93} {
		s.addVoice(voice{
			osc:   osc{step: hz * ratio / float64(s.rate)},
			sweep: 1,
			gain:  gain / float32(1+2*i),
			decay: s.decayFor(seconds / float64(1+i)),
		}, float32(i%2)*0.3-0.15)
	}
}

// Chirp plays a short rising chirp for a member arriving.
func (s *Synth) Chirp() {
	n := 0.12 * float64(s.rate)
	s.addVoice(voice{
		osc:   osc{step: 1200 / float64(s.rate)},
		sweep: math.Pow(2, 1/n),
		gain:  0.12,
		decay: s.decayFor(0.15),
	}, 0)
}

// maxVoices bounds the work a burst of Super Chats can cause.
const maxVoices = 64

func (s *Synth) addVoice(v voice, pan float32) {
	v.amp = 1
	v.left, v.right = 1-pan, 1+pan
	if len(s.voices) >= maxVoices {
		copy(s.voices, s.voices[1:])
		s.voices = s.voices[:maxVoices-1]
	}
	s.voices = append(s.voices, v)
}

// decayFor returns the per-sample multiplier that brings an envelope down
// by 60 dB in the given time.
func (s *Synth) decayFor(seconds float64) float32 {
	return float32(math.Pow(0.001, 1/(seconds*float64(s.rate))))
}

// Fill writes len(buf)/BytesPerFrame sample frames of interleaved s16le
// stereo into buf.
func (s *Synth) Fill(buf []byte) {
	frames := len(buf) / BytesPerFrame
	chordLen := uint64(chordSeconds * s.rate)
	for f := range frames {
		if c := int(s.sample / chordLen % uint64(len(chords))); c != s.chord {
			s.chord = c
			for i := range s.notes {
				s.notes[i].level = 0
			}
			for _, i := range s.chordNotes[c] {
				s.notes[i].level = 1
			}
		}
		swell := 0.75 + 0.25*s.lfo.next()
		var l, r float32
		for i := range s.notes {
			n := &s.notes[i]
			n.amp += (n.level - n.amp) * s.smooth
			if n.amp < 1e-4 && n.level == 0 {
				continue
			}
			v := (n.a.next() + n.b.next()) * n.amp * 0.045 * swell
			l += v * (1 - n.pan)
			r += v * (1 + n.pan)
		}
		live := s.voices[:0]
		for _, v := range s.voices {
			x := v.next() * v.amp * v.gain
			l += x * v.left
			r += x * v.right
			v.amp *= v.decay
			v.step *= v.sweep
			if v.amp > 1e-3 {
				live = append(live, v)
			}
		}
		s.voices = live
		binary.LittleEndian.PutUint16(buf[f*4:], uint16(toS16(l)))
		binary.LittleEndian.PutUint16(buf[f*4+2:], uint16(toS16(r)))
		s.sample++
	}
}

// toS16 soft-limits x so loud moments compress instead of clipping.
func toS16(x float32) int16 {
	y := math.Tanh(float64(x))
	return int16(y * 32000)
}

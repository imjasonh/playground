// Package show turns the broadcast's audience into the scene: one boid per
// viewer, a gold named boid per member, and effects for Super Chats and
// memberships.
package show

import (
	"fmt"
	"math"
	"math/rand/v2"

	"github.com/imjasonh/playground/stream-boids/internal/audio"
	"github.com/imjasonh/playground/stream-boids/internal/flock"
	"github.com/imjasonh/playground/stream-boids/internal/frame"
	"github.com/imjasonh/playground/stream-boids/internal/youtube"
)

// Config sets the limits on the boid count.
type Config struct {
	// Cap is the most boids, and so the most viewers drawn.
	Cap int
	// Min is the fewest boids, shown while there are fewer viewers.
	Min int
}

// maxBanners is how many thank-you banners can wait their turn.
const maxBanners = 8

// growRate is the fraction of the gap to the target count closed per
// second.
const growRate = 1.5

// Show owns the flock and the synth between frames. It is not safe for
// concurrent use.
type Show struct {
	cfg   Config
	flock *flock.Flock
	synth *audio.Synth

	target int
	// names[i] labels boid i. A member keeps their boid while they stay.
	names []string
	slot  map[string]int
	hud   frame.HUD
	hue   float64

	banners    []frame.Banner
	bannerLeft float64
	scene      frame.Scene
}

// New returns a Show that drives fl and synth.
func New(cfg Config, fl *flock.Flock, synth *audio.Synth) *Show {
	s := &Show{cfg: cfg, flock: fl, synth: synth, slot: map[string]int{}}
	s.target = s.clamp(0)
	return s
}

// Target is the boid count the show is moving toward.
func (s *Show) Target() int { return s.target }

func (s *Show) clamp(n int) int {
	return min(max(n, s.cfg.Min), s.cfg.Cap)
}

// Update applies the broadcast's state.
func (s *Show) Update(st youtube.State) {
	members := st.Members[:min(len(st.Members), s.cfg.Cap)]
	keep := make(map[string]bool, len(members))
	for _, m := range members {
		keep[m] = true
	}
	for i := 0; i < len(s.names); {
		if keep[s.names[i]] {
			i++
			continue
		}
		s.removeSlot(i)
	}
	for _, m := range members {
		if _, ok := s.slot[m]; !ok {
			s.slot[m] = len(s.names)
			s.names = append(s.names, m)
		}
	}

	s.hud = frame.HUD{Viewers: st.Viewers, ViewersKnown: st.ViewersKnown, Members: len(st.Members)}
	n := len(members)
	if st.ViewersKnown {
		n = max(n, st.Viewers)
	}
	s.target = s.clamp(n)
}

// removeSlot drops the member in slot i, moving the last member and their
// boid into it so every other member keeps the boid they had.
func (s *Show) removeSlot(i int) {
	last := len(s.names) - 1
	delete(s.slot, s.names[i])
	if i != last {
		s.names[i] = s.names[last]
		s.slot[s.names[i]] = i
		if last < s.flock.Len() {
			s.flock.Swap(i, last)
		}
	}
	s.names = s.names[:last]
}

// Event reacts to a chat event.
func (s *Show) Event(m youtube.Message) {
	name := m.Author.Name
	switch m.Type {
	case youtube.SuperChat, youtube.SuperSticker:
		tier := min(max(m.Tier, 1), 7)
		text := "sent a Super Sticker"
		switch {
		case m.Amount != "":
			text = "sent " + m.Amount
		case m.Type == youtube.SuperChat:
			text = "sent a Super Chat"
		}
		s.synth.Bell(tier)
		s.hue += 12 * float64(tier)
		s.kick(name, 0.1+0.035*float32(tier), 250+120*float32(tier))
		s.banner(frame.Banner{Name: name, Text: text, Tier: tier})
	case youtube.NewSponsor, youtube.MemberMilestone:
		text := "became a member"
		if m.Type == youtube.MemberMilestone {
			text = "celebrated a membership milestone"
		}
		s.synth.Chirp()
		s.kick(name, 0.08, 220)
		s.banner(frame.Banner{Name: name, Text: text})
	case youtube.MembershipGifting:
		text := "gifted a membership"
		if m.Gifts != 1 {
			text = fmt.Sprintf("gifted %d memberships", m.Gifts)
		}
		s.synth.Chirp()
		s.synth.Bell(min(max(m.Gifts/2, 1), 7))
		s.kick(name, 0.15, 400)
		s.banner(frame.Banner{Name: name, Text: text})
	}
}

// kick pushes the flock away from the member's boid, or from a random
// point for a viewer without one. radius is a fraction of the height.
func (s *Show) kick(name string, radius, strength float32) {
	var x, y float32
	if i, ok := s.slot[name]; ok && i < s.flock.Len() {
		x, y = s.flock.X[i], s.flock.Y[i]
	} else {
		x, y = rand.Float32()*s.flock.Width, rand.Float32()*s.flock.Height
	}
	s.flock.Kick(x, y, radius*s.flock.Height, strength)
}

func (s *Show) banner(b frame.Banner) {
	if len(s.banners) == maxBanners {
		return
	}
	if len(s.banners) == 0 {
		s.bannerLeft = bannerTime(b)
	}
	s.banners = append(s.banners, b)
}

// bannerTime is how long a banner shows; higher tiers stay longer.
func bannerTime(b frame.Banner) float64 {
	return 4 + 0.75*float64(b.Tier)
}

// Step advances the show by dt seconds and returns the scene to render.
// The scene is valid until the next call.
func (s *Show) Step(dt float64) *frame.Scene {
	if n := s.flock.Len(); n != s.target {
		gap := float64(s.target - n)
		change := int(math.Ceil(math.Abs(gap) * min(1, dt*growRate)))
		if gap < 0 {
			change = -change
		}
		s.flock.Resize(n + change)
	}

	if len(s.banners) > 0 {
		s.bannerLeft -= dt
		if s.bannerLeft <= 0 {
			s.banners = s.banners[1:]
			if len(s.banners) > 0 {
				s.bannerLeft = bannerTime(s.banners[0])
			}
		}
	}

	// A slow drift keeps the palette moving between Super Chats.
	s.hue = math.Mod(s.hue+dt*0.5, 256)
	s.flock.Step(float32(dt))

	s.scene.Flock = s.flock
	s.scene.Labels = s.names
	s.scene.HUD = s.hud
	s.scene.HueShift = uint8(s.hue)
	s.scene.Banner = nil
	if len(s.banners) > 0 {
		s.scene.Banner = &s.banners[0]
	}
	return &s.scene
}

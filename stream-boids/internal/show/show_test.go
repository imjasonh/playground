package show

import (
	"slices"
	"testing"

	"github.com/imjasonh/playground/stream-boids/internal/audio"
	"github.com/imjasonh/playground/stream-boids/internal/flock"
	"github.com/imjasonh/playground/stream-boids/internal/frame"
	"github.com/imjasonh/playground/stream-boids/internal/youtube"
)

const dt = 1.0 / 60

func newShow(cfg Config) *Show {
	return New(cfg, flock.New(1280, 720, flock.DefaultParams(), 1, 1), audio.New(48000))
}

// settle steps until the flock reaches its target.
func settle(t *testing.T, s *Show) *frame.Scene {
	t.Helper()
	var sc *frame.Scene
	for range 600 {
		sc = s.Step(dt)
		if s.flock.Len() == s.target {
			return sc
		}
	}
	t.Fatalf("flock has %d boids after 10 s, want %d", s.flock.Len(), s.target)
	return nil
}

func TestTarget(t *testing.T) {
	for _, tc := range []struct {
		name string
		st   youtube.State
		want int
	}{
		{"no state", youtube.State{}, 3},
		{"viewers", youtube.State{Viewers: 40, ViewersKnown: true}, 40},
		{"over cap", youtube.State{Viewers: 4000, ViewersKnown: true}, 100},
		{"under min", youtube.State{Viewers: 1, ViewersKnown: true}, 3},
		{"hidden count", youtube.State{Viewers: 0, Members: []string{"a", "b", "c", "d"}}, 4},
		{"members over viewers", youtube.State{Viewers: 2, ViewersKnown: true, Members: []string{"a", "b", "c", "d", "e"}}, 5},
	} {
		t.Run(tc.name, func(t *testing.T) {
			s := newShow(Config{Cap: 100, Min: 3})
			s.Update(tc.st)
			if s.Target() != tc.want {
				t.Errorf("Target = %d, want %d", s.Target(), tc.want)
			}
		})
	}
}

func TestCountChangesGradually(t *testing.T) {
	s := newShow(Config{Cap: 10000, Min: 0})
	s.Update(youtube.State{Viewers: 6000, ViewersKnown: true})
	s.Step(dt)
	if n := s.flock.Len(); n == 0 || n > 600 {
		t.Errorf("after one frame: %d boids, want a small step toward 6000", n)
	}
	settle(t, s)
	s.Update(youtube.State{Viewers: 10, ViewersKnown: true})
	settle(t, s)
}

func TestMembersKeepTheirBoids(t *testing.T) {
	s := newShow(Config{Cap: 50, Min: 20})
	s.Update(youtube.State{Members: []string{"ann", "bob", "cat", "dan"}})
	sc := settle(t, s)
	if !slices.Equal(sc.Labels, []string{"ann", "bob", "cat", "dan"}) {
		t.Fatalf("labels = %q", sc.Labels)
	}
	dx, dy := s.flock.X[3], s.flock.Y[3]

	// Bob leaves: Dan moves into Bob's slot, and his boid comes with him.
	s.Update(youtube.State{Members: []string{"dan", "cat", "ann", "eve"}})
	if !slices.Equal(s.names, []string{"ann", "dan", "cat", "eve"}) {
		t.Fatalf("labels = %q", s.names)
	}
	if s.flock.X[1] != dx || s.flock.Y[1] != dy {
		t.Error("Dan's label moved to a different boid")
	}
	if s.hud.Members != 4 {
		t.Errorf("HUD members = %d, want 4", s.hud.Members)
	}
}

func TestMembersOverCap(t *testing.T) {
	s := newShow(Config{Cap: 2, Min: 0})
	s.Update(youtube.State{Members: []string{"a", "b", "c"}})
	sc := settle(t, s)
	if len(sc.Labels) != 2 || sc.HUD.Members != 3 {
		t.Errorf("labels %q, HUD members %d; want 2 labels and 3 members counted", sc.Labels, sc.HUD.Members)
	}
}

func TestSuperChatBannerQueue(t *testing.T) {
	s := newShow(Config{Cap: 10, Min: 10})
	settle(t, s)
	s.Event(youtube.Message{Type: youtube.SuperChat, Author: youtube.Author{Name: "ann"}, Tier: 7, Amount: "$100.00"})
	s.Event(youtube.Message{Type: youtube.NewSponsor, Author: youtube.Author{Name: "bob"}})
	s.Event(youtube.Message{Type: youtube.TextMessage, Author: youtube.Author{Name: "cat"}})
	for range 20 {
		s.Event(youtube.Message{Type: youtube.SuperSticker, Author: youtube.Author{Name: "dan"}, Tier: 1})
	}
	if len(s.banners) != maxBanners {
		t.Errorf("%d banners queued, want %d", len(s.banners), maxBanners)
	}

	var shown []frame.Banner
	for range 60 * 60 {
		sc := s.Step(dt)
		if sc.Banner != nil && (len(shown) == 0 || shown[len(shown)-1] != *sc.Banner) {
			shown = append(shown, *sc.Banner)
		}
	}
	want := []frame.Banner{
		{Name: "ann", Text: "sent $100.00", Tier: 7},
		{Name: "bob", Text: "became a member"},
		{Name: "dan", Text: "sent a Super Sticker", Tier: 1},
	}
	if len(shown) < 3 || !slices.Equal(shown[:3], want) {
		t.Errorf("banners shown = %+v, want to start with %+v", shown, want)
	}
	if sc := s.Step(dt); sc.Banner != nil {
		t.Errorf("banner %+v still showing after a minute", sc.Banner)
	}
}

func TestSuperChatShiftsHue(t *testing.T) {
	s := newShow(Config{Cap: 10, Min: 10})
	before := s.Step(dt).HueShift
	s.Event(youtube.Message{Type: youtube.SuperChat, Author: youtube.Author{Name: "ann"}, Tier: 5, Amount: "$20.00"})
	if after := s.Step(dt).HueShift; after-before < 50 {
		t.Errorf("hue moved %d, want at least 50 for a tier 5 Super Chat", after-before)
	}
}

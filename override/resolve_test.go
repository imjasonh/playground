package override

import (
	"testing"
)

func TestResolutionCases(t *testing.T) {
	homes := []Faction{FactionIntelligence, FactionStrength, FactionSpeed}

	t.Run("direct_counter_rank_irrelevant", func(t *testing.T) {
		seats := emptySeats(homes)
		plays := []Play{
			{0, Card{FactionIntelligence, 1, 0}},
			{1, Card{FactionSpeed, 2, 1}},
		}
		w, _, steps, err := ResolveClash(plays, seats, 50)
		if err != nil || steps != 0 || w != 1 {
			t.Fatalf("want seat 1 win, got w=%d steps=%d err=%v", w, steps, err)
		}
	})

	t.Run("direct_counter_same_winning_suit", func(t *testing.T) {
		seats := emptySeats(homes)
		plays := []Play{
			{0, Card{FactionStrength, 13, 2}},
			{1, Card{FactionIntelligence, 7, 3}},
			{2, Card{FactionStrength, 5, 4}},
		}
		w, _, _, err := ResolveClash(plays, seats, 50)
		if err != nil || w != 1 {
			t.Fatalf("Intelligence beats Strength: want seat 1, got %d err=%v", w, err)
		}
	})

	t.Run("standoff_three_suits", func(t *testing.T) {
		seats := emptySeats(homes)
		plays := []Play{
			{0, Card{FactionIntelligence, 10, 5}},
			{1, Card{FactionStrength, 9, 6}},
			{2, Card{FactionSpeed, 13, 7}},
		}
		w, _, _, err := ResolveClash(plays, seats, 50)
		if err != nil || w != 2 {
			t.Fatalf("want seat 2 (Gold Speed), got %d err=%v", w, err)
		}
	})

	t.Run("ingenuity_standoff_steal", func(t *testing.T) {
		seats := emptySeats(homes)
		plays := []Play{
			{0, Card{FactionIngenuity, 13, 8}},
			{1, Card{FactionIntelligence, 12, 9}},
		}
		w, _, _, err := ResolveClash(plays, seats, 50)
		if err != nil || w != 0 {
			t.Fatalf("want Ingenuity steal, got %d err=%v", w, err)
		}
	})

	t.Run("home_boost_within_winning_suit", func(t *testing.T) {
		seats := emptySeats(homes)
		plays := []Play{
			{0, Card{FactionStrength, 10, 10}},
			{1, Card{FactionSpeed, 13, 11}},
			{2, Card{FactionStrength, 9, 12}},
		}
		w, _, _, err := ResolveClash(plays, seats, 50)
		if err != nil || w != 0 {
			t.Fatalf("want boosted Strength 10+3, got %d err=%v", w, err)
		}
	})

	t.Run("direct_counter_home_tie_war", func(t *testing.T) {
		seats := []Seat{
			{Home: FactionStrength, Hand: repeatCard(FactionSpeed, 4)},
			{Home: FactionSpeed, Hand: repeatCard(FactionSpeed, 4)},
			{Home: FactionIntelligence},
		}
		plays := []Play{
			{0, Card{FactionStrength, 8, 42}},
			{1, Card{FactionStrength, 11, 43}},
			{2, Card{FactionSpeed, 1, 44}},
		}
		w, pot, steps, err := ResolveClash(plays, seats, 50)
		if err != nil {
			t.Fatal(err)
		}
		if steps < 1 || len(pot) < 3 {
			t.Fatalf("want War, got steps=%d pot=%d winner=%d", steps, len(pot), w)
		}
	})

	t.Run("war_from_three_way_rank_tie", func(t *testing.T) {
		seats := []Seat{
			{Home: FactionIntelligence, Hand: repeatCard(FactionStrength, 10)},
			{Home: FactionStrength, Hand: repeatCard(FactionSpeed, 10)},
			{Home: FactionSpeed},
		}
		plays := []Play{
			{0, Card{FactionIntelligence, 10, 30}},
			{1, Card{FactionStrength, 10, 31}},
			{2, Card{FactionSpeed, 10, 32}},
		}
		_, pot, steps, err := ResolveClash(plays, seats, 50)
		if err != nil {
			t.Fatal(err)
		}
		if steps < 1 || len(pot) < 4 {
			t.Fatalf("want War chain, steps=%d pot=%d", steps, len(pot))
		}
	})
}

func emptySeats(homes []Faction) []Seat {
	s := make([]Seat, len(homes))
	for i, h := range homes {
		s[i].Home = h
	}
	return s
}

func repeatCard(f Faction, n int) []Card {
	h := make([]Card, n)
	for i := range h {
		h[i] = Card{Faction: f, Rank: 5, ID: 100 + i}
	}
	return h
}

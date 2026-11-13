package clash

import (
	"math/rand"
	"testing"
)

func TestNewDeck(t *testing.T) {
	deck := NewDeck()
	if len(deck) != DeckSize || DeckSize != 48 {
		t.Fatalf("deck has %d cards, want 48", len(deck))
	}
	perSuit := map[Suit]int{}
	for _, c := range deck {
		if c.Rank < LowRank || c.Rank > HighRank {
			t.Fatalf("rank %d out of range (Aces should be gone)", c.Rank)
		}
		perSuit[c.Suit]++
	}
	for _, s := range Suits {
		if perSuit[s] != 12 {
			t.Errorf("suit %s has %d cards, want 12", s, perSuit[s])
		}
	}
}

func TestBidAndResolve(t *testing.T) {
	// A 5, plus the Intelligence card in the pot and the played Intelligence
	// card: 5 + 1 + 1 = 7.
	got := bidTotal(Card{Intelligence, 5}, []Card{{Intelligence, 7}, {Strength, 4}}, Intelligence)
	if got != 7 {
		t.Errorf("bidTotal = %d, want 7", got)
	}

	seats := []Seat{{Home: Intelligence}, {Home: Strength}}

	// The higher card wins outright.
	neutral := []Card{{Speed, 7}, {Speed, 4}}
	if w := resolveRound(seats, []Card{{Speed, 6}, {Speed, 9}}, neutral); w != 1 {
		t.Errorf("higher bid should win, got winner %d", w)
	}

	// Equal cards, but only seat 0's Home (Intelligence) sits in the pot, so its
	// bonus breaks the tie.
	homePot := []Card{{Intelligence, 7}, {Speed, 4}}
	if w := resolveRound(seats, []Card{{Speed, 8}, {Speed, 8}}, homePot); w != 0 {
		t.Errorf("home bonus should break the tie for seat 0, got winner %d", w)
	}

	// Equal bids with no bonus to either side: no winner, the pot carries.
	if w := resolveRound(seats, []Card{{Speed, 8}, {Speed, 8}}, neutral); w != -1 {
		t.Errorf("tied bids should have no winner, got %d", w)
	}
}

// TestResolvability plays many games with assorted strategies and checks that
// each one ends with every card accounted for in exactly one place.
func TestResolvability(t *testing.T) {
	games := 20000
	if testing.Short() {
		games = 2000
	}
	rng := rand.New(rand.NewSource(1))
	strats := []Strategy{
		RandomCommit(), Competent(), Hoard(), Steal(), Sniper(), Bot(),
	}
	for _, players := range []int{2, 3, 4} {
		for g := 0; g < games; g++ {
			table := make([]Strategy, players)
			homes := make([]Suit, players)
			for i := 0; i < players; i++ {
				table[i] = strats[rng.Intn(len(strats))]
				homes[i] = Suits[i]
			}
			res, err := PlayGame(rng, table, homes)
			if err != nil {
				t.Fatalf("%d players, game %d: %v", players, g, err)
			}
			if res.CardsAccounted != DeckSize {
				t.Fatalf("%d players: %d cards accounted, want %d", players, res.CardsAccounted, DeckSize)
			}
		}
	}
}

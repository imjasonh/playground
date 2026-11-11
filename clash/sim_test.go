package clash

import (
	"math/rand"
	"testing"
)

// winRate returns how often strategy a outscores b in two-player games, counting
// a tie as half.
func winRate(rng *rand.Rand, a, b Strategy, games int) float64 {
	homes := []Suit{Intelligence, Strength}
	wins := 0.0
	for g := 0; g < games; g++ {
		res, err := PlayGame(rng, []Strategy{a, b}, homes)
		if err != nil {
			panic(err) // helper used only by tests
		}
		switch {
		case res.Scores[0] > res.Scores[1]:
			wins++
		case res.Scores[0] == res.Scores[1]:
			wins += 0.5
		}
	}
	return wins / float64(games)
}

// seatShares returns each seat's win share when every seat plays the same
// strategy, which should be even if the deal has no positional bias.
func seatShares(rng *rand.Rand, s Strategy, players, games int) []float64 {
	shares := make([]float64, players)
	table := make([]Strategy, players)
	homes := make([]Suit, players)
	for i := 0; i < players; i++ {
		table[i] = s
		homes[i] = Suits[i]
	}
	for g := 0; g < games; g++ {
		res, err := PlayGame(rng, table, homes)
		if err != nil {
			panic(err)
		}
		best, winners := -1, 0
		for _, sc := range res.Scores {
			if sc > best {
				best, winners = sc, 1
			} else if sc == best {
				winners++
			}
		}
		for i, sc := range res.Scores {
			if sc == best {
				shares[i] += 1.0 / float64(winners)
			}
		}
	}
	for i := range shares {
		shares[i] /= float64(games)
	}
	return shares
}

// TestForceBid checks the must-bid rule: a seat with cards that would pass is
// made to commit its single lowest card, while an empty hand commits nothing.
func TestForceBid(t *testing.T) {
	hand := []Card{{Strength, 9}, {Speed, 3}, {Intelligence, 11}}
	if got := forceBid(hand, nil); len(got) != 1 || got[0] != 1 {
		t.Errorf("forceBid on a pass = %v, want [1] (the Speed 3, lowest)", got)
	}
	if got := forceBid(hand, []int{2}); len(got) != 1 || got[0] != 2 {
		t.Errorf("forceBid left an existing bid alone: got %v, want [2]", got)
	}
	if got := forceBid(nil, nil); len(got) != 0 {
		t.Errorf("forceBid on an empty hand = %v, want nothing", got)
	}
}

// TestMustBidPunishesPassing checks that refusing to invest bleeds you dry: a
// seat that always tries to pass is forced to shed its lowest card each clash
// and loses nearly every game to a competent player.
func TestMustBidPunishesPassing(t *testing.T) {
	passer := Strategy{"passer", func(View, *rand.Rand) []int { return nil }}
	rng := rand.New(rand.NewSource(8))
	if r := winRate(rng, Competent(), passer, scale(2000, 10000)); r < 0.95 {
		t.Errorf("competent vs always-pass win rate %.3f, want > 0.95 (passing should bleed out)", r)
	}
}

// TestHandRefill checks the hand tops back up from the draw pile between
// clashes: a seat that spends one card a round keeps a full hand for the whole
// game, since its draw pile outlasts the rounds, and the hand never exceeds the
// cap.
func TestHandRefill(t *testing.T) {
	var sizes []int
	watch := Strategy{"watch-one", func(v View, _ *rand.Rand) []int {
		sizes = append(sizes, len(v.Hand))
		if len(v.Hand) == 0 {
			return nil
		}
		return []int{0}
	}}
	rng := rand.New(rand.NewSource(5))
	if _, err := PlayGame(rng, []Strategy{watch, Competent()}, []Suit{Intelligence, Strength}); err != nil {
		t.Fatal(err)
	}
	_, _, rounds, _ := dealPlan(2)
	if len(sizes) != rounds {
		t.Fatalf("saw %d clashes, want %d", len(sizes), rounds)
	}
	for rd, n := range sizes {
		if n > handCap {
			t.Errorf("clash %d: hand held %d cards, over the cap of %d", rd, n, handCap)
		}
		if n != handCap {
			t.Errorf("clash %d: hand held %d cards, want a full %d (draw pile should refill it)", rd, n, handCap)
		}
	}
}

func scale(short, full int) int {
	if testing.Short() {
		return short
	}
	return full
}

// TestSeatBalance checks the deal has no positional advantage: identical
// strategies win about equally often from every seat.
func TestSeatBalance(t *testing.T) {
	rng := rand.New(rand.NewSource(2))
	games := scale(3000, 20000)
	for _, players := range []int{2, 3, 4} {
		shares := seatShares(rng, Competent(), players, games)
		fair := 1.0 / float64(players)
		for i, sh := range shares {
			if sh < fair-0.04 || sh > fair+0.04 {
				t.Errorf("%d players seat %d win share %.3f, want ~%.3f", players, i, sh, fair)
			}
		}
	}
}

// botShare returns a competent player's win share from seat 0 against a table
// filled out with solo bots, counting a shared win as a fraction.
func botShare(rng *rand.Rand, players, games int) float64 {
	table := []Strategy{Competent()}
	homes := []Suit{Suits[0]}
	for i := 1; i < players; i++ {
		table = append(table, Bot())
		homes = append(homes, Suits[i])
	}
	share := 0.0
	for g := 0; g < games; g++ {
		res, err := PlayGame(rng, table, homes)
		if err != nil {
			panic(err)
		}
		best, winners := -1, 0
		for _, sc := range res.Scores {
			if sc > best {
				best, winners = sc, 1
			} else if sc == best {
				winners++
			}
		}
		if res.Scores[0] == best {
			share += 1.0 / float64(winners)
		}
	}
	return share / float64(games)
}

// TestBotBeatable checks the closed-pile solo bot gives a real game at every
// table size: a competent player stays clearly favored over an even share, yet
// the bots still take enough games that they are not a pushover. The naive
// "always lowest" rule, by contrast, is trivial to beat.
func TestBotBeatable(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	games := scale(3000, 20000)

	for _, players := range []int{2, 3, 4} {
		fair := 1.0 / float64(players)
		share := botShare(rng, players, games)
		if share < fair+0.10 {
			t.Errorf("%d players: competent win share %.3f, want clearly above even share %.3f", players, share, fair)
		}
		if share > 0.97 {
			t.Errorf("%d players: competent win share %.3f, bots look like a pushover", players, share)
		}
	}

	tooEasy := winRate(rng, Competent(), BotLowest(), games)
	if tooEasy < 0.85 {
		t.Errorf("competent vs always-lowest win rate %.3f, want > 0.85 (should be trivial)", tooEasy)
	}
}

// TestNoDominantStrategy checks that no strategy beats the whole field: every
// strategy loses to at least one other, which is the signature of a game with
// real decisions rather than one correct line.
func TestNoDominantStrategy(t *testing.T) {
	rng := rand.New(rand.NewSource(4))
	games := scale(2000, 12000)
	field := []Strategy{Hoard(), Steal(), Sniper(), Competent(), Bot()}

	worstOfBest := 0.0
	for _, a := range field {
		worst := 1.0
		for _, b := range field {
			if a.Name == b.Name {
				continue
			}
			if r := winRate(rng, a, b, games); r < worst {
				worst = r
			}
		}
		t.Logf("%-10s worst matchup win rate %.3f", a.Name, worst)
		if worst > worstOfBest {
			worstOfBest = worst
		}
	}
	// A dominant strategy would win every matchup; flag anything that beats its
	// whole field by a wide margin.
	if worstOfBest > 0.68 {
		t.Errorf("a strategy wins its worst matchup %.3f of the time (>0.68): looks dominant", worstOfBest)
	}
}

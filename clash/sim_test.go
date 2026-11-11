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

// TestBotBeatable checks the printed solo bot gives a real game: a competent
// player beats it clearly but not trivially, while the naive "always lowest"
// rule is far too easy.
func TestBotBeatable(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	games := scale(3000, 20000)

	good := winRate(rng, Competent(), Bot(), games)
	if good < 0.55 || good > 0.80 {
		t.Errorf("competent vs bot win rate %.3f, want in [0.55, 0.80]", good)
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

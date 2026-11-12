package clash

import (
	"math/rand"
	"testing"
)

// winShares returns each seat's slice of the win, splitting a tie evenly among
// the seats that hold the most cards.
func winShares(res GameResult) []float64 {
	shares := make([]float64, len(res.Counts))
	best, winners := -1, 0
	for _, c := range res.Counts {
		if c > best {
			best, winners = c, 1
		} else if c == best {
			winners++
		}
	}
	for i, c := range res.Counts {
		if c == best {
			shares[i] = 1.0 / float64(winners)
		}
	}
	return shares
}

// winRate returns how often strategy a holds more cards than b in two-player
// games, counting a tie as half.
func winRate(rng *rand.Rand, a, b Strategy, games int) float64 {
	homes := []Suit{Intelligence, Strength}
	wins := 0.0
	for g := 0; g < games; g++ {
		res, err := PlayGame(rng, []Strategy{a, b}, homes)
		if err != nil {
			panic(err) // helper used only by tests
		}
		wins += winShares(res)[0]
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
		for i, sh := range winShares(res) {
			shares[i] += sh
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

// TestDeal checks the even split: the 48-card deck deals into equal stacks for
// two, three, and four players, leaving a 20-, 12-, or 8-card pile once each
// seat takes its four-card hand.
func TestDeal(t *testing.T) {
	want := map[int]int{2: 20, 3: 12, 4: 8}
	for _, players := range []int{2, 3, 4} {
		pile, ok := deal(players)
		if !ok {
			t.Errorf("%d players: no deal", players)
			continue
		}
		if pile != want[players] {
			t.Errorf("%d players: pile %d, want %d", players, pile, want[players])
		}
		if stack := pile + handCap; stack != DeckSize/players {
			t.Errorf("%d players: stack %d, want %d", players, stack, DeckSize/players)
		}
	}
}

// TestGameTerminates checks that every game ends on its own, well under the
// safety cap. Each clash discards one committed card per seat for good, so a
// game can last at most DeckSize / players clashes no matter how the pot
// recirculates.
func TestGameTerminates(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	games := scale(3000, 20000)
	strats := []Strategy{RandomCommit(), Competent(), Hoard(), Steal(), Sniper(), Bot()}
	for _, players := range []int{2, 3, 4} {
		limit := DeckSize / players
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
			if res.Clashes < 1 || res.Clashes > limit {
				t.Fatalf("%d players: %d clashes, want 1..%d", players, res.Clashes, limit)
			}
			if res.Clashes >= safetyCap {
				t.Fatalf("%d players: hit the safety cap at %d clashes", players, res.Clashes)
			}
		}
	}
}

// TestHandDepletes checks the hand mechanic: it starts and stays full of four
// while the pile has cards to refill it, and the game runs on attrition, not a
// fixed clash count. A seat sees a shrinking hand only once its pile is spent.
func TestHandDepletes(t *testing.T) {
	var sizes []int
	watch := Strategy{"watch", func(v View, _ *rand.Rand) int {
		sizes = append(sizes, len(v.Hand))
		return 0
	}}
	rng := rand.New(rand.NewSource(5))
	res, err := PlayGame(rng, []Strategy{watch, Competent()}, []Suit{Intelligence, Strength})
	if err != nil {
		t.Fatal(err)
	}
	if len(sizes) != res.Clashes {
		t.Fatalf("watched %d clashes, game ran %d", len(sizes), res.Clashes)
	}
	if sizes[0] != handCap {
		t.Errorf("first clash hand held %d cards, want a full %d", sizes[0], handCap)
	}
	for rd, n := range sizes {
		if n < 1 || n > handCap {
			t.Errorf("clash %d: hand held %d cards, want 1..%d", rd, n, handCap)
		}
	}
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
			if sh < fair-0.05 || sh > fair+0.05 {
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
		share += winShares(res)[0]
	}
	return share / float64(games)
}

// TestBotBeatable checks the closed-pile solo bot gives a real game at every
// table size: a competent player stays clearly favored over an even share, yet
// the bots still take enough games that they are not a pushover. The naive
// "always lowest" rule, by contrast, is clearly beatable.
func TestBotBeatable(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	games := scale(3000, 20000)

	for _, players := range []int{2, 3, 4} {
		fair := 1.0 / float64(players)
		share := botShare(rng, players, games)
		if share < fair*1.2 {
			t.Errorf("%d players: competent win share %.3f, want clearly above even share %.3f", players, share, fair)
		}
		if share > 0.97 {
			t.Errorf("%d players: competent win share %.3f, bots look like a pushover", players, share)
		}
	}

	easy := winRate(rng, Competent(), BotLowest(), games)
	if easy < 0.65 {
		t.Errorf("competent vs always-lowest win rate %.3f, want > 0.65 (should be clearly beatable)", easy)
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

// mixedShares returns each seat's win share for a fixed table of distinct
// strategies, counting a shared win as a fraction.
func mixedShares(rng *rand.Rand, table []Strategy, games int) []float64 {
	homes := make([]Suit, len(table))
	for i := range homes {
		homes[i] = Suits[i]
	}
	shares := make([]float64, len(table))
	for g := 0; g < games; g++ {
		res, err := PlayGame(rng, table, homes)
		if err != nil {
			panic(err)
		}
		for i, sh := range winShares(res) {
			shares[i] += sh
		}
	}
	for i := range shares {
		shares[i] /= float64(games)
	}
	return shares
}

// combos calls fn with each k-combination of the indices in [0, n).
func combos(n, k int, fn func([]int)) {
	pick := make([]int, 0, k)
	var rec func(start int)
	rec = func(start int) {
		if len(pick) == k {
			fn(pick)
			return
		}
		for i := start; i < n; i++ {
			pick = append(pick, i)
			rec(i + 1)
			pick = pick[:len(pick)-1]
		}
	}
	rec(0)
}

// TestNoDominantStrategyMultiplayer checks the field stays balanced at three-
// and four-handed tables, not only heads-up. Each thinking strategy is seated
// with distinct opponents across every combination, and none may take much over
// a fair share.
func TestNoDominantStrategyMultiplayer(t *testing.T) {
	rng := rand.New(rand.NewSource(6))
	games := scale(2000, 12000)
	field := []Strategy{Hoard(), Steal(), Sniper(), Competent()}

	for _, players := range []int{3, 4} {
		fair := 1.0 / float64(players)
		sum := make([]float64, len(field))
		seen := make([]int, len(field))
		combos(len(field), players, func(pick []int) {
			table := make([]Strategy, players)
			for seat, idx := range pick {
				table[seat] = field[idx]
			}
			shares := mixedShares(rng, table, games)
			for seat, idx := range pick {
				sum[idx] += shares[seat]
				seen[idx]++
			}
		})
		for i, s := range field {
			mean := sum[i] / float64(seen[i])
			t.Logf("%d players: %-10s mean share %.3f (fair %.3f)", players, s.Name, mean, fair)
			if mean > fair*1.6 {
				t.Errorf("%d players: %s takes mean share %.3f, over 1.6x the fair share %.3f: looks dominant", players, s.Name, mean, fair)
			}
		}
	}
}

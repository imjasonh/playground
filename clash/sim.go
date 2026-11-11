package clash

import (
	"fmt"
	"math/rand"
	"sort"
)

// GameResult summarizes one finished game.
type GameResult struct {
	Players    int
	Rounds     int
	Carryovers int   // clashes that tied and pushed their pot forward
	Scores     []int // pips captured per seat
	Winner     int   // seat with the most pips, or -1 on a tie

	ScoredPips     int
	SetAsidePips   int // pips left in an unresolved final pot
	DiscardedPips  int // pips of committed cards, which are spent
	HandLeftPips   int
	CardsAccounted int // every dealt card, found in exactly one place
}

// dealPlan gives the hand and ante-pile sizes for a player count. Each plan
// uses all 48 cards evenly.
func dealPlan(players int) (hand, rounds int, ok bool) {
	switch players {
	case 2:
		return 15, 9, true
	case 3:
		return 10, 6, true
	case 4:
		return 7, 5, true
	default:
		return 0, 0, false
	}
}

func normalizeIdx(idx []int, n int) []int {
	seen := make(map[int]bool, len(idx))
	out := make([]int, 0, len(idx))
	for _, j := range idx {
		if j >= 0 && j < n && !seen[j] {
			seen[j] = true
			out = append(out, j)
		}
	}
	sort.Ints(out)
	return out
}

// removeIdx returns hand without the cards at the ascending indices in drop.
func removeIdx(hand []Card, drop []int) []Card {
	if len(drop) == 0 {
		return hand
	}
	out := make([]Card, 0, len(hand)-len(drop))
	k := 0
	for i, c := range hand {
		if k < len(drop) && drop[k] == i {
			k++
			continue
		}
		out = append(out, c)
	}
	return out
}

// PlayGame runs one full game. strategies drive the seats and homes gives each
// seat's Home suit; both must have 2 to 4 entries and the homes must differ.
func PlayGame(rng *rand.Rand, strategies []Strategy, homes []Suit) (GameResult, error) {
	players := len(strategies)
	if players < 2 || players > 4 {
		return GameResult{}, fmt.Errorf("clash needs 2 to 4 players, got %d", players)
	}
	if len(homes) != players {
		return GameResult{}, fmt.Errorf("got %d homes for %d players", len(homes), players)
	}
	seen := make(map[Suit]bool, players)
	for _, h := range homes {
		if seen[h] {
			return GameResult{}, fmt.Errorf("duplicate Home suit %s", h)
		}
		seen[h] = true
	}
	handSize, rounds, ok := dealPlan(players)
	if !ok {
		return GameResult{}, fmt.Errorf("no deal plan for %d players", players)
	}

	deck := NewDeck()
	rng.Shuffle(len(deck), func(i, j int) { deck[i], deck[j] = deck[j], deck[i] })
	seats := make([]Seat, players)
	pos := 0
	for i := range seats {
		seats[i].Home = homes[i]
		seats[i].Hand = append([]Card(nil), deck[pos:pos+handSize]...)
		pos += handSize
		seats[i].Ante = append([]Card(nil), deck[pos:pos+rounds]...)
		pos += rounds
	}

	var discarded, carry []Card
	carryovers := 0
	for rd := 0; rd < rounds; rd++ {
		pot := make([]Card, 0, players+len(carry))
		for i := range seats {
			pot = append(pot, seats[i].Ante[rd])
		}
		pot = append(pot, carry...)

		commits := make([][]Card, players)
		for i := range seats {
			v := View{Pot: pot, Hand: seats[i].Hand, Home: seats[i].Home, Opponents: players - 1}
			idx := normalizeIdx(strategies[i].Pick(v, rng), len(seats[i].Hand))
			commit := make([]Card, 0, len(idx))
			for _, j := range idx {
				commit = append(commit, seats[i].Hand[j])
			}
			seats[i].Hand = removeIdx(seats[i].Hand, idx)
			commits[i] = commit
			discarded = append(discarded, commit...)
		}

		out := resolveRound(seats, commits, pot)
		if out.winner >= 0 {
			seats[out.winner].Scored = append(seats[out.winner].Scored, pot...)
			carry = nil
		} else {
			carry = pot
			carryovers++
		}
	}
	setAside := carry

	res := GameResult{
		Players:    players,
		Rounds:     rounds,
		Carryovers: carryovers,
		Scores:     make([]int, players),
		Winner:     -1,
	}
	cards := len(discarded) + len(setAside)
	best, ties := -1, 0
	for i := range seats {
		res.Scores[i] = pips(seats[i].Scored)
		res.ScoredPips += res.Scores[i]
		res.HandLeftPips += pips(seats[i].Hand)
		cards += len(seats[i].Scored) + len(seats[i].Hand)
		switch {
		case res.Scores[i] > best:
			best, ties, res.Winner = res.Scores[i], 1, i
		case res.Scores[i] == best:
			ties++
		}
	}
	if ties != 1 {
		res.Winner = -1
	}
	res.SetAsidePips = pips(setAside)
	res.DiscardedPips = pips(discarded)
	res.CardsAccounted = cards
	return res, nil
}

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
	HandLeftPips   int // pips still in hands and draw piles at the end
	CardsAccounted int // every dealt card, found in exactly one place
}

// dealPlan gives the starting hand, draw-pile, and ante-pile sizes for a player
// count, from one even rule: deal all 48 cards into equal stacks, keep handCap
// in hand, and split the rest of the stack into two equal piles, one draw and
// one ante. Because every stack (24, 16, or 12) minus the hand is even, the
// split is exact, and the ante always equals the draw. The hand refills to
// handCap from the draw pile after each clash, so hand+draw is the whole bid
// budget; with ante equal to draw, that budget beats the number of rounds by
// exactly handCap at every table size.
func dealPlan(players int) (hand, draw, rounds int, ok bool) {
	if players < 2 || players > 4 || DeckSize%players != 0 {
		return 0, 0, 0, false
	}
	stack := DeckSize / players
	rest := stack - handCap
	ante := rest / 2
	return handCap, rest - ante, ante, true
}

// handCap is the number of cards a seat holds and refills to each clash.
const handCap = 4

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

// forceBid enforces the must-bid rule: every clash a seat commits at least one
// card. When a strategy would pass but still holds cards, it is made to commit
// its single lowest card, so refusing to invest bleeds a card for nothing. A
// seat that has emptied its hand has nothing to commit and is left alone.
func forceBid(hand []Card, idx []int) []int {
	if len(idx) > 0 || len(hand) == 0 {
		return idx
	}
	low := 0
	for i, c := range hand {
		if c.Rank < hand[low].Rank {
			low = i
		}
	}
	return []int{low}
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
	handSize, drawSize, rounds, ok := dealPlan(players)
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
		seats[i].Draw = append([]Card(nil), deck[pos:pos+drawSize]...)
		pos += drawSize
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
			idx = forceBid(seats[i].Hand, idx)
			commit := make([]Card, 0, len(idx))
			for _, j := range idx {
				commit = append(commit, seats[i].Hand[j])
			}
			seats[i].Hand = removeIdx(seats[i].Hand, idx)
			commits[i] = commit
			discarded = append(discarded, commit...)
			for len(seats[i].Hand) < handCap && len(seats[i].Draw) > 0 {
				seats[i].Hand = append(seats[i].Hand, seats[i].Draw[0])
				seats[i].Draw = seats[i].Draw[1:]
			}
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
		res.HandLeftPips += pips(seats[i].Hand) + pips(seats[i].Draw)
		cards += len(seats[i].Scored) + len(seats[i].Hand) + len(seats[i].Draw)
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

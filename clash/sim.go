package clash

import (
	"fmt"
	"math/rand"
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

// pickCard asks a strategy which card to play and returns a valid hand index.
// A seat always plays exactly one card, so a strategy that returns an index out
// of range falls back to the top of the hand. An empty hand returns -1.
func pickCard(s Strategy, v View, rng *rand.Rand) int {
	if len(v.Hand) == 0 {
		return -1
	}
	j := s.Pick(v, rng)
	if j < 0 || j >= len(v.Hand) {
		return 0
	}
	return j
}

// removeAt returns hand without the card at index j.
func removeAt(hand []Card, j int) []Card {
	out := make([]Card, 0, len(hand)-1)
	out = append(out, hand[:j]...)
	return append(out, hand[j+1:]...)
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

		played := make([]Card, players)
		for i := range seats {
			v := View{Pot: pot, Hand: seats[i].Hand, Home: seats[i].Home, Opponents: players - 1}
			j := pickCard(strategies[i], v, rng)
			if j < 0 {
				continue
			}
			played[i] = seats[i].Hand[j]
			seats[i].Hand = removeAt(seats[i].Hand, j)
			discarded = append(discarded, played[i])
			if len(seats[i].Draw) > 0 {
				seats[i].Hand = append(seats[i].Hand, seats[i].Draw[0])
				seats[i].Draw = seats[i].Draw[1:]
			}
		}

		out := resolveRound(seats, played, pot)
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

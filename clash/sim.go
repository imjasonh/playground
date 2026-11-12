package clash

import (
	"fmt"
	"math/rand"
)

// GameResult summarizes one finished game.
type GameResult struct {
	Players    int
	Clashes    int   // clashes played before a seat ran out of cards
	Carryovers int   // clashes that tied and pushed their pot forward
	Counts     []int // cards each seat still holds at the end (hand plus pile)
	Winner     int   // seat with the most cards, or -1 on a tie

	Discarded      int // committed cards spent over the whole game
	OnTable        int // cards left in an unresolved pot when the game ended
	CardsAccounted int // every dealt card, found in exactly one place
}

// handCap is the number of cards a seat holds and refills toward each clash.
const handCap = 4

// safetyCap bounds the clash loop so a bug can never hang a test. A real game
// always ends far sooner: every clash permanently discards one committed card
// per seat, so play lasts at most DeckSize / players clashes.
const safetyCap = 1000

// deal gives the face-down pile size for a player count. The 48-card deck
// divides evenly among two, three, or four players, and every stack is larger
// than a starting hand, so the deal always works: take handCap cards into the
// hand and the rest is the pile.
func deal(players int) (pile int, ok bool) {
	if players < 2 || players > 4 || DeckSize%players != 0 {
		return 0, false
	}
	stack := DeckSize / players
	if stack <= handCap {
		return 0, false
	}
	return stack - handCap, true
}

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

// refill tops a seat's hand back toward the cap from its pile, taking cards off
// the top. The hand stays full until the pile runs dry, then shrinks as the
// seat keeps playing.
func refill(s *Seat) {
	for len(s.Hand) < handCap && len(s.Pile) > 0 {
		s.Hand = append(s.Hand, s.Pile[0])
		s.Pile = s.Pile[1:]
	}
}

// PlayGame runs one full game. strategies drive the seats and homes gives each
// seat's Home suit; both must have 2 to 4 entries and the homes must differ.
//
// Each seat holds one face-down pile and a hand of handCap. A clash feeds the
// pot one card off the top of every pile, then every seat commits one card from
// its hand. The highest bid wins the pot onto the bottom of its pile; the
// committed cards are spent for good. A tie carries the pot into the next
// clash. The game ends the moment a seat cannot play, and the seat holding the
// most cards wins.
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
	pileSize, ok := deal(players)
	if !ok {
		return GameResult{}, fmt.Errorf("no deal for %d players", players)
	}

	deck := NewDeck()
	rng.Shuffle(len(deck), func(i, j int) { deck[i], deck[j] = deck[j], deck[i] })
	seats := make([]Seat, players)
	pos := 0
	for i := range seats {
		seats[i].Home = homes[i]
		seats[i].Hand = append([]Card(nil), deck[pos:pos+handCap]...)
		pos += handCap
		seats[i].Pile = append([]Card(nil), deck[pos:pos+pileSize]...)
		pos += pileSize
	}

	var carry []Card
	clashes, carryovers, discarded := 0, 0, 0
	for clashes < safetyCap {
		if anyEmptyHand(seats) {
			break
		}
		clashes++

		pot := append([]Card(nil), carry...)
		for i := range seats {
			if len(seats[i].Pile) > 0 {
				pot = append(pot, seats[i].Pile[0])
				seats[i].Pile = seats[i].Pile[1:]
			}
		}

		played := make([]Card, players)
		for i := range seats {
			v := View{Pot: pot, Hand: seats[i].Hand, Home: seats[i].Home, Opponents: players - 1}
			j := pickCard(strategies[i], v, rng)
			played[i] = seats[i].Hand[j]
			seats[i].Hand = removeAt(seats[i].Hand, j)
			discarded++
		}

		winner := resolveRound(seats, played, pot)
		if winner >= 0 {
			seats[winner].Pile = append(seats[winner].Pile, pot...)
			carry = nil
		} else {
			carry = pot
			carryovers++
		}
		for i := range seats {
			refill(&seats[i])
		}
	}

	res := GameResult{
		Players:    players,
		Clashes:    clashes,
		Carryovers: carryovers,
		Counts:     make([]int, players),
		Winner:     -1,
		Discarded:  discarded,
		OnTable:    len(carry),
	}
	cards := discarded + len(carry)
	best, ties := -1, 0
	for i := range seats {
		res.Counts[i] = len(seats[i].Hand) + len(seats[i].Pile)
		cards += res.Counts[i]
		switch {
		case res.Counts[i] > best:
			best, ties, res.Winner = res.Counts[i], 1, i
		case res.Counts[i] == best:
			ties++
		}
	}
	if ties != 1 {
		res.Winner = -1
	}
	res.CardsAccounted = cards
	return res, nil
}

// anyEmptyHand reports whether a seat has no card left to play, which ends the
// game.
func anyEmptyHand(seats []Seat) bool {
	for i := range seats {
		if len(seats[i].Hand) == 0 {
			return true
		}
	}
	return false
}

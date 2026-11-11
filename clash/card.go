// Package clash is a simulation harness for the card game Clash. It proves the
// game resolves (every game ends and every card is accounted for) and that no
// single strategy dominates, including the simple bot used for solo play.
package clash

import "fmt"

// Suit is one of Clash's four factions. The factions have no pecking order; a
// suit matters only as a player's Home and for card values. Any suit may be a
// Home suit.
type Suit int

// The four suits.
const (
	Intelligence Suit = iota
	Strength
	Speed
	Ingenuity
)

// Suits lists every suit in deal order.
var Suits = []Suit{Intelligence, Strength, Speed, Ingenuity}

func (s Suit) String() string {
	switch s {
	case Intelligence:
		return "Intelligence"
	case Strength:
		return "Strength"
	case Speed:
		return "Speed"
	case Ingenuity:
		return "Ingenuity"
	default:
		return fmt.Sprintf("Suit(%d)", int(s))
	}
}

// Rank bounds. The Ace (rank 1) is pulled from every suit and used as an inert
// marker for who holds that Home, so play runs from 2 up to Gold (13).
const (
	LowRank  = 2
	HighRank = 13
)

// DeckSize is the number of playing cards once the four Aces are set aside.
const DeckSize = 4 * (HighRank - LowRank + 1)

// Card is one playing card. Its value in a clash is its rank.
type Card struct {
	Suit Suit
	Rank int
}

// RankName gives the printed name of a rank: numbers for 2 through 10, then
// Bronze, Silver, and Gold for 11, 12, and 13.
func RankName(rank int) string {
	switch rank {
	case 11:
		return "Bronze"
	case 12:
		return "Silver"
	case 13:
		return "Gold"
	default:
		return fmt.Sprintf("%d", rank)
	}
}

func (c Card) String() string { return fmt.Sprintf("%s of %s", RankName(c.Rank), c.Suit) }

// NewDeck returns the 48 playing cards, Aces excluded.
func NewDeck() []Card {
	deck := make([]Card, 0, DeckSize)
	for _, s := range Suits {
		for r := LowRank; r <= HighRank; r++ {
			deck = append(deck, Card{Suit: s, Rank: r})
		}
	}
	return deck
}

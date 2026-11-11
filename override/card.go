package override

// Faction is a card suit in OVERRIDE.
type Faction int

const (
	FactionIntelligence Faction = iota
	FactionStrength
	FactionSpeed
	FactionIngenuity
)

// RankAce is the lowest rank; RankGold (King) is the highest.
const (
	RankAce  = 1
	RankGold = 13
)

// Card is one card from the standard 52-card mapping used by the simulator.
type Card struct {
	Faction Faction
	Rank    int
	ID      int
}

// Real returns whether the card belongs to a faction in the dominance cycle.
func (c Card) Real() bool {
	return c.Faction != FactionIngenuity
}

// Seat holds one player or bot at the table.
type Seat struct {
	Home  Faction
	Hand  []Card
	Score []Card
	IsBot bool
}

// Play is one seat's committed card for a Clash.
type Play struct {
	Seat int
	Card Card
}

var beats = map[Faction]Faction{
	FactionIntelligence: FactionStrength,
	FactionStrength:     FactionSpeed,
	FactionSpeed:        FactionIntelligence,
}

// EffectiveRank applies the Home +3 boost for real Home-suit cards.
func EffectiveRank(c Card, home Faction) int {
	bonus := 0
	if c.Real() && c.Faction == home {
		bonus = 3
	}
	return c.Rank + bonus
}

// NewDeck builds the 52 cards (13 per faction).
func NewDeck() []Card {
	var deck []Card
	id := 0
	for f := FactionIntelligence; f <= FactionIngenuity; f++ {
		for rank := RankAce; rank <= RankGold; rank++ {
			deck = append(deck, Card{Faction: f, Rank: rank, ID: id})
			id++
		}
	}
	return deck
}

func distinctRealSuits(plays []Play) map[Faction]struct{} {
	out := make(map[Faction]struct{})
	for _, p := range plays {
		if p.Card.Real() {
			out[p.Card.Faction] = struct{}{}
		}
	}
	return out
}

func directCounterWinner(a, b Faction) Faction {
	if beats[a] == b {
		return a
	}
	if beats[b] == a {
		return b
	}
	panic("invalid suit pair")
}

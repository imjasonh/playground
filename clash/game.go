package clash

// Seat is one player or bot at the table.
type Seat struct {
	Home   Suit
	Hand   []Card // the cards to choose one from each clash, refilled to the cap
	Draw   []Card // face-down pile that refills the hand
	Ante   []Card // one card fed to the pot each round
	Scored []Card // cards won, tallied by pips at the end
}

// pips totals the ranks of a set of cards.
func pips(cards []Card) int {
	total := 0
	for _, c := range cards {
		total += c.Rank
	}
	return total
}

// homeCount counts cards of a given suit.
func homeCount(cards []Card, home Suit) int {
	n := 0
	for _, c := range cards {
		if c.Suit == home {
			n++
		}
	}
	return n
}

// bidTotal is a seat's bid for one clash: the rank of the single card it
// played, plus one for every card of its Home suit in the pot and one more when
// the card it played is itself a Home-suit card.
func bidTotal(played Card, pot []Card, home Suit) int {
	bid := played.Rank + homeCount(pot, home)
	if played.Suit == home {
		bid++
	}
	return bid
}

// roundOutcome reports who won a clash.
type roundOutcome struct {
	winner  int // -1 when the top bids tie
	potPips int
}

// resolveRound settles one clash. The pot is already assembled (this round's
// antes plus any cards carried from an earlier tie). played holds the one card
// each seat put down; the highest bid wins. A tie for the top leaves no winner,
// so the caller carries the pot forward.
func resolveRound(seats []Seat, played []Card, pot []Card) roundOutcome {
	out := roundOutcome{winner: -1, potPips: pips(pot)}
	best, ties := -1, 0
	for i := range seats {
		b := bidTotal(played[i], pot, seats[i].Home)
		switch {
		case b > best:
			best, ties, out.winner = b, 1, i
		case b == best:
			ties++
		}
	}
	if ties != 1 {
		out.winner = -1
	}
	return out
}

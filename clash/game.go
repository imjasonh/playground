package clash

// Seat is one player or bot at the table.
type Seat struct {
	Home Suit
	Hand []Card // the cards to choose one from each clash, refilled from the pile
	Pile []Card // face-down stack: feeds one card to the pot and refills the hand
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

// resolveRound settles one clash and returns the winning seat, or -1 when the
// top bids tie. The pot is already assembled (this clash's antes plus any cards
// carried from an earlier tie). played holds the one card each seat put down;
// the highest bid wins. A tie for the top leaves no winner, so the caller
// carries the pot forward.
func resolveRound(seats []Seat, played []Card, pot []Card) int {
	winner, best, ties := -1, -1, 0
	for i := range seats {
		b := bidTotal(played[i], pot, seats[i].Home)
		switch {
		case b > best:
			best, ties, winner = b, 1, i
		case b == best:
			ties++
		}
	}
	if ties != 1 {
		return -1
	}
	return winner
}

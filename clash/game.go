package clash

// Seat is one player or bot at the table.
type Seat struct {
	Home   Suit
	Hand   []Card // the cards in hand right now, refilled to the cap each round
	Draw   []Card // face-down pile that refills the hand; the rest of the budget
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

// bidTotal is a seat's bid: the pips of the cards it committed, plus one for
// every card of its Home suit in the pot and one for every Home-suit card it
// committed.
func bidTotal(commit, pot []Card, home Suit) int {
	return pips(commit) + homeCount(pot, home) + homeCount(commit, home)
}

// roundOutcome reports who won a clash and the committed cards each seat spent.
type roundOutcome struct {
	winner  int // -1 when the top bids tie
	spent   [][]Card
	potPips int
}

// resolveRound settles one clash. The pot is already assembled (this round's
// antes plus any cards carried from an earlier tie). Each seat's strategy
// picks cards to commit from its hand; the highest bid wins. A tie leaves no
// winner so the caller carries the pot forward.
func resolveRound(seats []Seat, commits [][]Card, pot []Card) roundOutcome {
	out := roundOutcome{winner: -1, spent: commits, potPips: pips(pot)}
	best, ties := -1, 0
	for i := range seats {
		b := bidTotal(commits[i], pot, seats[i].Home)
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

package override

import (
	"fmt"
)

const defaultMaxWarDepth = 500

// ResolveClash applies the v2 hierarchy, including War chains.
// seats must hold the current hand state; hands are mutated during War.
func ResolveClash(plays []Play, seats []Seat, maxDepth int) (winner int, pot []Card, warSteps int, err error) {
	if maxDepth <= 0 {
		maxDepth = defaultMaxWarDepth
	}
	homes := make([]Faction, len(seats))
	for i := range seats {
		homes[i] = seats[i].Home
	}

	pot = cardsFromPlays(plays)

	winner, warTied := hierarchy(plays, homes)
	if winner >= 0 {
		return winner, pot, 0, nil
	}

	tied := make(map[int]struct{}, len(warTied))
	for _, s := range warTied {
		tied[s] = struct{}{}
	}

	initialWarTied := append([]int(nil), warTied...)

	for depth := 0; depth < maxDepth; depth++ {
		warSteps++
		var fighters []Play
		stillTied := make(map[int]struct{})

		for seat := range tied {
			h := len(seats[seat].Hand)
			switch {
			case h >= 2:
				burn := seats[seat].Hand[0]
				fight := seats[seat].Hand[1]
				seats[seat].Hand = seats[seat].Hand[2:]
				pot = append(pot, burn, fight)
				fighters = append(fighters, Play{Seat: seat, Card: fight})
				stillTied[seat] = struct{}{}
			case h == 1:
				fight := seats[seat].Hand[0]
				seats[seat].Hand = seats[seat].Hand[1:]
				pot = append(pot, fight)
				fighters = append(fighters, Play{Seat: seat, Card: fight})
				stillTied[seat] = struct{}{}
			}
		}

		tied = stillTied
		if len(tied) == 0 {
			w, e := splitAmongOrig(plays, initialWarTied, homes)
			return w, pot, warSteps, e
		}
		if len(tied) == 1 {
			for s := range tied {
				return s, pot, warSteps, nil
			}
		}

		winner, warTied = hierarchy(fighters, homes)
		if winner >= 0 {
			return winner, pot, warSteps, nil
		}

		tied = make(map[int]struct{}, len(warTied))
		for _, s := range warTied {
			tied[s] = struct{}{}
		}
	}
	return -1, pot, warSteps, fmt.Errorf("war exceeded max depth %d", maxDepth)
}

func cardsFromPlays(plays []Play) []Card {
	out := make([]Card, len(plays))
	for i, p := range plays {
		out[i] = p.Card
	}
	return out
}

// hierarchy returns winner seat >= 0, or -1 with warTied seats.
func hierarchy(plays []Play, homes []Faction) (winner int, warTied []int) {
	real := distinctRealSuits(plays)
	if len(real) == 2 {
		var suits [2]Faction
		i := 0
		for s := range real {
			suits[i] = s
			i++
		}
		winSuit := directCounterWinner(suits[0], suits[1])
		var winners []Play
		for _, p := range plays {
			if p.Card.Faction == winSuit {
				winners = append(winners, p)
			}
		}
		if len(winners) == 1 {
			return winners[0].Seat, nil
		}
		_, tied := bestAmong(winners, homes)
		if len(tied) == 1 {
			return tied[0], nil
		}
		return -1, tied
	}

	_, tied := bestAmong(plays, homes)
	if len(tied) == 1 {
		return tied[0], nil
	}
	return -1, tied
}

func bestAmong(plays []Play, homes []Faction) (best int, tied []int) {
	best = -1
	for _, p := range plays {
		r := EffectiveRank(p.Card, homes[p.Seat])
		if r > best {
			best = r
			tied = []int{p.Seat}
		} else if r == best {
			tied = append(tied, p.Seat)
		}
	}
	return best, tied
}

func splitAmongOrig(plays []Play, warTied []int, homes []Faction) (int, error) {
	set := make(map[int]struct{}, len(warTied))
	for _, s := range warTied {
		set[s] = struct{}{}
	}
	var orig []Play
	for _, p := range plays {
		if _, ok := set[p.Seat]; ok {
			orig = append(orig, p)
		}
	}
	if len(orig) == 0 {
		return 0, fmt.Errorf("war split with no original tied plays")
	}
	_, tied := bestAmong(orig, homes)
	return tied[0], nil
}

package clash

import (
	"math/rand"
	"sort"
)

// View is what a seat sees before it commits: the pot on the table, its own
// hand, its Home suit, and how many opponents it faces. Everyone's Home suit is
// public, so a strategy that cares about an opponent's Home reads it off the
// pot and the table.
type View struct {
	Pot       []Card
	Hand      []Card
	Home      Suit
	Opponents int
}

// Strategy picks which hand cards (by index) a seat commits to a clash.
type Strategy struct {
	Name string
	Pick func(v View, rng *rand.Rand) []int
}

func potPips(v View) int { return pips(v.Pot) }

func byRankDesc(hand []Card) []int {
	idx := make([]int, len(hand))
	for i := range idx {
		idx[i] = i
	}
	sort.Slice(idx, func(a, b int) bool { return hand[idx[a]].Rank > hand[idx[b]].Rank })
	return idx
}

func byRankAsc(hand []Card) []int {
	idx := byRankDesc(hand)
	for i, j := 0, len(idx)-1; i < j; i, j = i+1, j-1 {
		idx[i], idx[j] = idx[j], idx[i]
	}
	return idx
}

// BotLowest always commits its single lowest card. It is included to show that
// the obvious weakest rule is far too easy to beat.
func BotLowest() Strategy {
	return Strategy{"bot-lowest", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		return []int{byRankAsc(v.Hand)[0]}
	}}
}

// Bot is the solo bot printed in the rules, and its whole rule is a glance at
// the pot: it commits its highest card, and a second-highest as well when the
// pot shows its own Home suit. No judgment of a pot's worth, just a suit check.
// A thinking player beats it clearly without walking over it.
func Bot() Strategy {
	return Strategy{"bot", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		n := 1
		for _, c := range v.Pot {
			if c.Suit == v.Home {
				n = 2
				break
			}
		}
		return byRankDesc(v.Hand)[:min(n, len(v.Hand))]
	}}
}

// Hoard concedes cheap pots and spends its two highest cards on dear ones.
func Hoard() Strategy {
	return Strategy{"hoard", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		players := v.Opponents + 1
		if potPips(v) < 6*players {
			return nil
		}
		d := byRankDesc(v.Hand)
		return d[:min(2, len(d))]
	}}
}

// Steal grabs cheap and middling pots with a single mid card and overbids the
// dear ones with three high cards.
func Steal() Strategy {
	return Strategy{"steal", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		players := v.Opponents + 1
		if potPips(v) >= 10*players {
			d := byRankDesc(v.Hand)
			return d[:min(3, len(d))]
		}
		asc := byRankAsc(v.Hand)
		return []int{asc[len(asc)/2]}
	}}
}

// Sniper concedes everything but the very richest pots, then overcommits.
func Sniper() Strategy {
	return Strategy{"sniper", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		players := v.Opponents + 1
		if potPips(v) >= 13*players {
			d := byRankDesc(v.Hand)
			return d[:min(3, len(d))]
		}
		return nil
	}}
}

// Competent is a sensible thinking line: value each pot (its pips plus your own
// Home bump), concede the cheap ones, and win the rest with the fewest cards
// that should carry them. It stands in for a person playing well.
func Competent() Strategy {
	return Strategy{"competent", func(v View, _ *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		players := v.Opponents + 1
		value := potPips(v) + homeCount(v.Pot, v.Home)
		if value < 6*players {
			return nil
		}
		fair := value/players + 2
		d := byRankDesc(v.Hand)
		picked := make([]int, 0, 3)
		tot := 0
		for _, j := range d {
			picked = append(picked, j)
			tot += v.Hand[j].Rank
			if v.Hand[j].Suit == v.Home {
				tot++
			}
			if tot >= fair || len(picked) >= 3 {
				break
			}
		}
		return picked
	}}
}

// RandomCommit commits a random handful (zero to three cards). It exercises odd
// commits in the resolvability checks.
func RandomCommit() Strategy {
	return Strategy{"random", func(v View, rng *rand.Rand) []int {
		if len(v.Hand) == 0 {
			return nil
		}
		k := rng.Intn(min(4, len(v.Hand)+1))
		return rng.Perm(len(v.Hand))[:k]
	}}
}

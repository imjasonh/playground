package clash

import (
	"math/rand"
	"sort"
)

// View is what a seat sees before it plays: the pot on the table, its own
// hand, its Home suit, and how many opponents it faces. Everyone's Home suit is
// public, so a strategy that cares about an opponent's Home reads it off the
// pot and the table.
type View struct {
	Pot       []Card
	Hand      []Card
	Home      Suit
	Opponents int
}

// Strategy picks which one card (by hand index) a seat plays in a clash.
type Strategy struct {
	Name string
	Pick func(v View, rng *rand.Rand) int
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

// lowestIdx is the index of the weakest card by rank; highestIdx the strongest.
func lowestIdx(hand []Card) int  { return byRankAsc(hand)[0] }
func highestIdx(hand []Card) int { return byRankDesc(hand)[0] }

// BotLowest always plays its single weakest card. It is included to show that
// the obvious give-up-every-clash rule is far too easy to beat.
func BotLowest() Strategy {
	return Strategy{"bot-lowest", func(v View, _ *rand.Rand) int {
		return lowestIdx(v.Hand)
	}}
}

// Bot is the solo bot printed in the rules. Its hand is a closed, face-down
// pile that nobody manages: each clash it flips the top card and plays it, with
// no judgment of a pot's worth and no choosing. The pile is dealt in shuffled
// order, so index 0 is always the top. A flipped card is as likely to be high
// or low as any other, so a thinking player who saves strong cards for rich
// pots beats it clearly at every table size without walking over it.
func Bot() Strategy {
	return Strategy{"bot", func(v View, _ *rand.Rand) int {
		return 0
	}}
}

// Hoard concedes cheap pots with its weakest card and slams dear ones with its
// strongest.
func Hoard() Strategy {
	return Strategy{"hoard", func(v View, _ *rand.Rand) int {
		players := v.Opponents + 1
		if potPips(v) < 6*players {
			return lowestIdx(v.Hand)
		}
		return highestIdx(v.Hand)
	}}
}

// Steal tries to grab ordinary pots cheaply with a middling card and plays its
// strongest only for the dear ones.
func Steal() Strategy {
	return Strategy{"steal", func(v View, _ *rand.Rand) int {
		players := v.Opponents + 1
		if potPips(v) >= 10*players {
			return highestIdx(v.Hand)
		}
		asc := byRankAsc(v.Hand)
		return asc[len(asc)/2]
	}}
}

// Sniper concedes everything but the very richest pots, then plays its
// strongest card.
func Sniper() Strategy {
	return Strategy{"sniper", func(v View, _ *rand.Rand) int {
		players := v.Opponents + 1
		if potPips(v) >= 13*players {
			return highestIdx(v.Hand)
		}
		return lowestIdx(v.Hand)
	}}
}

// Competent is a sensible thinking line: value each pot (its pips plus your own
// Home bump), concede the cheap ones with your weakest card, and win the rest
// with the lowest card that should carry them, saving your best for later. It
// stands in for a person playing well.
func Competent() Strategy {
	return Strategy{"competent", func(v View, _ *rand.Rand) int {
		players := v.Opponents + 1
		value := potPips(v) + homeCount(v.Pot, v.Home)
		if value < 6*players {
			return lowestIdx(v.Hand)
		}
		target := value/players + 2
		for _, j := range byRankAsc(v.Hand) {
			bid := v.Hand[j].Rank
			if v.Hand[j].Suit == v.Home {
				bid++
			}
			if bid >= target {
				return j
			}
		}
		return highestIdx(v.Hand)
	}}
}

// RandomCommit plays a random card. It exercises odd choices in the
// resolvability checks.
func RandomCommit() Strategy {
	return Strategy{"random", func(v View, rng *rand.Rand) int {
		return rng.Intn(len(v.Hand))
	}}
}

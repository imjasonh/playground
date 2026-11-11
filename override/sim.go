package override

import (
	"fmt"
	"math/rand"
)

// GameResult summarizes one simulated full game.
type GameResult struct {
	Clashes               int
	WarSteps              int
	ReinforcementCaptures int
	ScoredTotal           int
	HandLeft              int
	CenterLeft            int
	WinnerSeat            int
	SeatScores            [3]int
}

// PlayRandomGame runs one full game with random legal bot plays.
func PlayRandomGame(rng *rand.Rand, humanSeats int) (GameResult, error) {
	if humanSeats < 1 || humanSeats > 3 {
		return GameResult{}, fmt.Errorf("humanSeats must be 1..3, got %d", humanSeats)
	}

	deck := NewDeck()
	rng.Shuffle(len(deck), func(i, j int) { deck[i], deck[j] = deck[j], deck[i] })

	homes := [3]Faction{FactionIntelligence, FactionStrength, FactionSpeed}
	var seats [3]Seat
	for i := range seats {
		seats[i].Home = homes[i]
		seats[i].IsBot = i >= humanSeats
	}

	for i := range seats {
		seats[i].Hand = append(seats[i].Hand, deck[:5]...)
		deck = deck[5:]
	}

	var res GameResult
	const maxClashes = 10_000

	for res.Clashes < maxClashes {
		var holders []int
		for i := range seats {
			if len(seats[i].Hand) > 0 {
				holders = append(holders, i)
			}
		}
		if len(holders) < 2 {
			break
		}

		var plays []Play
		for _, i := range holders {
			h := seats[i].Hand
			pick := rng.Intn(len(h))
			card := h[pick]
			seats[i].Hand = append(h[:pick], h[pick+1:]...)
			plays = append(plays, Play{Seat: i, Card: card})
		}

		winner, pot, warSteps, err := ResolveClash(plays, seats[:], defaultMaxWarDepth)
		if err != nil {
			return res, err
		}
		res.WarSteps += warSteps
		res.Clashes++

		for _, c := range pot {
			seats[winner].Score = append(seats[winner].Score, c)
		}

		winCard := plays[winnerCardIndex(plays, winner)]
		if winCard.Card.Real() && winCard.Card.Faction == seats[winner].Home && len(deck) > 0 {
			seats[winner].Score = append(seats[winner].Score, deck[0])
			deck = deck[1:]
			res.ReinforcementCaptures++
		}

		for _, i := range holders {
			for len(seats[i].Hand) < 5 && len(deck) > 0 {
				seats[i].Hand = append(seats[i].Hand, deck[0])
				deck = deck[1:]
			}
		}
	}

	for i := range seats {
		res.SeatScores[i] = len(seats[i].Score)
		res.ScoredTotal += len(seats[i].Score)
		res.HandLeft += len(seats[i].Hand)
	}
	res.CenterLeft = len(deck)

	best := res.SeatScores[0]
	res.WinnerSeat = 0
	for i := 1; i < 3; i++ {
		if res.SeatScores[i] > best {
			best = res.SeatScores[i]
			res.WinnerSeat = i
		}
	}

	total := res.ScoredTotal + res.HandLeft + res.CenterLeft
	if total > 52 {
		return res, fmt.Errorf("card conservation failed: %d cards accounted for", total)
	}
	return res, nil
}

func winnerCardIndex(plays []Play, winner int) int {
	for i, p := range plays {
		if p.Seat == winner {
			return i
		}
	}
	return 0
}

// BalanceStats aggregates Monte Carlo outcomes.
type BalanceStats struct {
	Games            int
	WinsBySeat       [3]int
	WinsByHome       [3]int
	AvgClashes       float64
	AvgReinforcement float64
}

// RunBalance runs games and returns aggregate stats (3p random bots).
func RunBalance(rng *rand.Rand, games int) (BalanceStats, error) {
	var s BalanceStats
	for g := 0; g < games; g++ {
		res, err := PlayRandomGame(rng, 3)
		if err != nil {
			return s, err
		}
		s.Games++
		s.WinsBySeat[res.WinnerSeat]++
		homes := [3]Faction{FactionIntelligence, FactionStrength, FactionSpeed}
		s.WinsByHome[homes[res.WinnerSeat]]++
		s.AvgClashes += float64(res.Clashes)
		s.AvgReinforcement += float64(res.ReinforcementCaptures)
	}
	if s.Games > 0 {
		s.AvgClashes /= float64(s.Games)
		s.AvgReinforcement /= float64(s.Games)
	}
	return s, nil
}

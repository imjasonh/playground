package override

import (
	"math/rand"
	"testing"
)

func gamesPerMode(testingShort bool) int {
	if testingShort {
		return 2_000
	}
	return 20_000
}

func TestResolvability(t *testing.T) {
	rng := rand.New(rand.NewSource(0x0D00))
	modes := []struct {
		name   string
		humans int
	}{
		{"3p", 3},
		{"2p", 2},
		{"1p", 1},
	}

	n := gamesPerMode(testing.Short())
	for _, mode := range modes {
		mode := mode
		t.Run(mode.name, func(t *testing.T) {
			var maxWar, maxClashes int
			for i := 0; i < n; i++ {
				res, err := PlayRandomGame(rng, mode.humans)
				if err != nil {
					t.Fatalf("game %d: %v", i, err)
				}
				if res.ScoredTotal+res.HandLeft+res.CenterLeft > 52 {
					t.Fatalf("game %d: conservation %d", i, res.ScoredTotal+res.HandLeft+res.CenterLeft)
				}
				if res.WarSteps > maxWar {
					maxWar = res.WarSteps
				}
				if res.Clashes > maxClashes {
					maxClashes = res.Clashes
				}
			}
			t.Logf("completed %d games; max clashes=%d max war steps=%d", n, maxClashes, maxWar)
		})
	}
}

func TestResolvabilityAdversarialWar(t *testing.T) {
	homes := []Faction{FactionIntelligence, FactionStrength, FactionSpeed}
	for trial := 0; trial < 500; trial++ {
		seats := []Seat{
			{Home: homes[0], Hand: repeatCard(FactionIngenuity, 5)},
			{Home: homes[1], Hand: repeatCard(FactionIngenuity, 5)},
			{Home: homes[2]},
		}
		plays := []Play{
			{0, Card{FactionIntelligence, 10, 300}},
			{1, Card{FactionStrength, 10, 301}},
			{2, Card{FactionSpeed, 10, 302}},
		}
		_, _, steps, err := ResolveClash(plays, seats, 200)
		if err != nil {
			t.Fatalf("trial %d: %v", trial, err)
		}
		if steps == 0 {
			t.Fatalf("trial %d: expected War steps", trial)
		}
	}
}

func TestBalance(t *testing.T) {
	rng := rand.New(rand.NewSource(0xBA17))
	games := 8_000
	if testing.Short() {
		games = 800
	}
	stats, err := RunBalance(rng, games)
	if err != nil {
		t.Fatal(err)
	}

	// Symmetric random play: no Home faction should dominate wins.
	lo, hi := 0.22, 0.45
	if testing.Short() {
		lo, hi = 0.12, 0.55
	}
	for f := FactionIntelligence; f <= FactionSpeed; f++ {
		share := float64(stats.WinsByHome[f]) / float64(stats.Games)
		if share < lo || share > hi {
			t.Errorf("home %d win share %.3f outside [%.2f, %.2f]", f, share, lo, hi)
		}
	}

	// Game length should stay near the 52-card budget (roughly 10–17 clashes at 3p).
	if stats.AvgClashes < 8 || stats.AvgClashes > 18 {
		t.Errorf("avg clashes %.2f outside [8, 18]", stats.AvgClashes)
	}

	// Reinforcement is a small swing, not most of the score pile.
	if stats.AvgReinforcement < 0.5 || stats.AvgReinforcement > 8 {
		t.Errorf("avg reinforcement captures %.2f outside [0.5, 8]", stats.AvgReinforcement)
	}

	t.Logf("balance: games=%d avg_clashes=%.2f avg_reinforcement=%.2f wins_by_home=%v",
		stats.Games, stats.AvgClashes, stats.AvgReinforcement, stats.WinsByHome)
}

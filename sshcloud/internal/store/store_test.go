package store

import "testing"

func TestStrategyConstants(t *testing.T) {
	if StrategyDrain != "drain" || StrategyKick != "kick" {
		t.Fatalf("unexpected strategies %q %q", StrategyDrain, StrategyKick)
	}
}

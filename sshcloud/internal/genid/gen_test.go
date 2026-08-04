package genid

import "testing"

func TestAgentAppRoundTrip(t *testing.T) {
	t.Parallel()
	if got := AgentApp("myapp", ""); got != "myapp" {
		t.Fatalf("got %q", got)
	}
	if got := AgentApp("myapp", "gabc"); got != "myapp.gabc" {
		t.Fatalf("got %q", got)
	}
	app, gen := SplitAgentApp("myapp.gabc")
	if app != "myapp" || gen != "gabc" {
		t.Fatalf("split %q %q", app, gen)
	}
	app, gen = SplitAgentApp("fortune")
	if app != "fortune" || gen != "" {
		t.Fatalf("split fortune: %q %q", app, gen)
	}
}

func TestNewUnique(t *testing.T) {
	a, b := New(), New()
	if a == "" || a == b {
		t.Fatalf("gens %q %q", a, b)
	}
	if a[0] != 'g' {
		t.Fatalf("prefix %q", a)
	}
}

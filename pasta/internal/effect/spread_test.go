package effect

import (
	"testing"

	"github.com/imjasonh/playground/pasta/internal/match"
)

func TestInterpolateWithCaptures_stripsSpreadDots(t *testing.T) {
	caps := match.Captures{}
	text := map[string]string{"src": "...xs"}
	got := interpolateWithCaptures("{...@src}", caps, text)
	if got != "{...xs}" {
		t.Fatalf("got %q, want `{...xs}`", got)
	}
	got = interpolateWithCaptures("[...@src]", caps, text)
	if got != "[...xs]" {
		t.Fatalf("got %q, want `[...xs]`", got)
	}
	// Without a leading ... in the template, leave capture text alone.
	got = interpolateWithCaptures("@src", caps, text)
	if got != "...xs" {
		t.Fatalf("got %q, want `...xs`", got)
	}
}

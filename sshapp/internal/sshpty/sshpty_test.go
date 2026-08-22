package sshpty

import "testing"

func TestNormalize(t *testing.T) {
	term, w, h := Normalize("dumb", 0, 0)
	if term != DefaultTerm || w != DefaultWidth || h != DefaultHeight {
		t.Fatalf("got %q %dx%d", term, w, h)
	}
	term, w, h = Normalize("xterm-256color", 120, 40)
	if term != "xterm-256color" || w != 120 || h != 40 {
		t.Fatalf("got %q %dx%d", term, w, h)
	}
}

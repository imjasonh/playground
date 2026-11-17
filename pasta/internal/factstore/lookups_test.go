package factstore_test

import (
	"testing"

	"github.com/imjasonh/playground/pasta/internal/factstore"
)

func TestLookupsOverlapAdded(t *testing.T) {
	s := factstore.New()
	a := parse(t, "go", "a.go", "package a\n\nfunc f() {\n\tx = y\n\tsink(x)\n}\n")
	b := parse(t, "go", "b.go", "package b\n\nfunc g() {\n\tz = y\n\tx = 1\n}\n")

	var la, lb factstore.Lookups
	ra := factstore.Recorder{Store: s, Lookups: &la}
	rb := factstore.Recorder{Store: s, Lookups: &lb}
	if ra.Has(a.ident(t, "x", 1), "tainted") {
		t.Fatal("x has a fact in an empty store")
	}
	rb.Has(b.ident(t, "z", 0), "tainted")

	mark := s.Mark()
	if !s.Added(mark).Empty() {
		t.Fatal("Added reports entries before any emit")
	}
	s.Emit("tainted", b.ident(t, "x", 0), nil)
	added := s.Added(mark)
	if !la.Overlaps(added) {
		t.Error("a lookup of x in a.go doesn't overlap a new fact on x in b.go")
	}
	if lb.Overlaps(added) {
		t.Error("a lookup of z overlaps a new fact on x")
	}
	if !ra.Has(a.ident(t, "x", 1), "tainted") {
		t.Error("Recorder doesn't answer from the store")
	}

	mark = s.Mark()
	s.Emit("tainted", b.ident(t, "x", 0), map[string]any{"again": true})
	if !s.Added(mark).Empty() {
		t.Error("emitting an existing fact again adds an entry")
	}
}

func TestLookupsOverlapAddedRange(t *testing.T) {
	s := factstore.New()
	a := parse(t, "go", "a.go", "package a\n\nfunc f() { g(1 + 2) }\n")
	var l factstore.Lookups
	call := a.ident(t, "g", 0).Parent()
	if call.Type() != "call_expression" {
		t.Fatalf("got %s, want call_expression", call.Type())
	}
	factstore.Recorder{Store: s, Lookups: &l}.Has(call, "k")

	mark := s.Mark()
	s.Emit("k", call.ChildByFieldName("function"), nil)
	if l.Overlaps(s.Added(mark)) {
		t.Error("a lookup of g(1 + 2) overlaps a new fact on g")
	}
	s.Emit("k", call, nil)
	if !l.Overlaps(s.Added(mark)) {
		t.Error("a lookup of g(1 + 2) doesn't overlap a new fact on it")
	}
}

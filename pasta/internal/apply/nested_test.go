package apply

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/effect"
)

func TestResolveNested_keepsInnermost(t *testing.T) {
	ops := []effect.Op{
		{Rule: "outer", Start: 0, End: 20, Text: "OUTER"},
		{Rule: "inner", Start: 5, End: 10, Text: "INNER"},
	}
	got, err := ResolveNested(ops)
	if err != nil {
		t.Fatal(err)
	}
	if len(got) != 1 || got[0].Rule != "inner" {
		t.Fatalf("got %+v, want only inner", got)
	}
}

func TestApply_nestedWholeNode(t *testing.T) {
	src := []byte("Array<Array<T>>")
	// Outer covers whole string; inner covers Array<T> at bytes 6..14.
	ops := []effect.Op{
		{Rule: "outer", Start: 0, End: 15, Text: "Array<T>[]"},
		{Rule: "inner", Start: 6, End: 14, Text: "T[]"},
	}
	got, err := Apply(src, ops, dsl.RewriteOpts{})
	if err != nil {
		t.Fatal(err)
	}
	want := "Array<T[]>"
	if string(got) != want {
		t.Fatalf("got %q, want %q", got, want)
	}
}

func TestApply_partialOverlapStillErrors(t *testing.T) {
	src := []byte(strings.Repeat("x", 20))
	_, err := Apply(src, []effect.Op{
		{Rule: "a", Start: 0, End: 10, Text: "A"},
		{Rule: "b", Start: 5, End: 15, Text: "B"},
	}, dsl.RewriteOpts{})
	if err == nil || !strings.Contains(err.Error(), "conflicting edits") {
		t.Fatalf("want conflicting edits error, got %v", err)
	}
}

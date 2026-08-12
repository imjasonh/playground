package prefilter

import (
	"reflect"
	"testing"

	"github.com/imjasonh/pasta/internal/dsl"
)

func TestForRule_eqAndWithin(t *testing.T) {
	rule := &dsl.Rule{
		Name: "prefer_shorthand",
		Match: dsl.Pattern{
			Node: []string{"generic_type"},
			Where: []dsl.Predicate{
				{Op: "eq", Args: []dsl.Arg{{Str: "@outer"}, {Str: "Array"}}},
			},
		},
		RequireSubstring: []string{"ReadonlyArray"},
		Rewrite: &dsl.Rewrite{Edits: []dsl.Edit{
			{Within: "_root", Token: "var", ReplaceWith: "let"},
		}},
	}
	f := ForRule(rule)
	wantAll := []string{"ReadonlyArray", "Array", "var"}
	if !reflect.DeepEqual(f.AllOf, wantAll) {
		t.Fatalf("AllOf = %v, want %v", f.AllOf, wantAll)
	}
	if len(f.AnyOf) != 0 {
		t.Fatalf("AnyOf = %v, want empty", f.AnyOf)
	}
}

func TestForRule_matchesAlternation(t *testing.T) {
	rule := &dsl.Rule{
		Match: dsl.Pattern{
			Where: []dsl.Predicate{
				{Op: "matches", Args: []dsl.Arg{{Str: "@op"}, {Str: "==|!="}}},
			},
		},
	}
	f := ForRule(rule)
	if !reflect.DeepEqual(f.AnyOf, []string{"==", "!="}) {
		t.Fatalf("AnyOf = %v, want [== !=]", f.AnyOf)
	}
}

func TestForRule_skipsCaptureRefsAndComplexRegex(t *testing.T) {
	rule := &dsl.Rule{
		Match: dsl.Pattern{
			Where: []dsl.Predicate{
				{Op: "eq", Args: []dsl.Arg{{Str: "@a"}, {Str: "@b"}}},
				{Op: "matches", Args: []dsl.Arg{{Str: "@x"}, {Str: "foo.*bar"}}},
			},
		},
	}
	f := ForRule(rule)
	if !f.Empty() {
		t.Fatalf("expected empty filter, got %+v", f)
	}
}

func TestMayMatch(t *testing.T) {
	filters := []Filter{
		{AllOf: []string{"Array"}},
		{AllOf: []string{"Object", "assign"}},
	}
	if MayMatch([]byte("const x: number[] = []"), filters) {
		t.Fatal("expected no match without Array/Object.assign")
	}
	if !MayMatch([]byte("type T = Array<number>"), filters) {
		t.Fatal("expected match for Array")
	}
	if !MayMatch([]byte("Object.assign({}, x)"), filters) {
		t.Fatal("expected match for Object.assign")
	}
	// Unfilterable rule forces a parse.
	if !MayMatch([]byte("anything"), []Filter{{}, {AllOf: []string{"zzz"}}}) {
		t.Fatal("empty filter must force MayMatch=true")
	}
	if MayMatch([]byte("x"), nil) {
		t.Fatal("no filters → false")
	}
}

func TestFilterMatch_anyOf(t *testing.T) {
	f := Filter{AnyOf: []string{"==", "!="}}
	if f.Match([]byte("a + b")) {
		t.Fatal("expected miss")
	}
	if !f.Match([]byte("a == b")) {
		t.Fatal("expected hit on ==")
	}
	if !f.Match([]byte("a != b")) {
		t.Fatal("expected hit on !=")
	}
}

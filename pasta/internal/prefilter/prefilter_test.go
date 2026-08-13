package prefilter

import (
	"reflect"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
)

func TestForRule_eqAndRequireSubstring(t *testing.T) {
	rule := &dsl.Rule{
		Name: "prefer_shorthand",
		Match: dsl.Pattern{
			Node: []string{"generic_type"},
			Where: []dsl.Predicate{
				{Op: "eq", Args: []dsl.Arg{{Str: "@outer"}, {Str: "Array"}}},
			},
		},
		RequireSubstring: []string{"ReadonlyArray"},
		// within tokens must NOT be inferred — diagnose can fire without them.
		Rewrite: &dsl.Rewrite{Edits: []dsl.Edit{
			{Within: "_root", Token: "var", ReplaceWith: "let"},
		}},
	}
	f := ForRule(rule)
	wantAll := []string{"ReadonlyArray", "Array"}
	if !reflect.DeepEqual(f.AllOf, wantAll) {
		t.Fatalf("AllOf = %v, want %v", f.AllOf, wantAll)
	}
	if len(f.AnyOf) != 0 {
		t.Fatalf("AnyOf = %v, want empty", f.AnyOf)
	}
}

func TestForRule_withinTokenNotRequired(t *testing.T) {
	rule := &dsl.Rule{
		Match:    dsl.Pattern{Node: []string{"variable_declaration"}},
		Diagnose: &dsl.Diagnostic{Message: "use let"},
		Rewrite: &dsl.Rewrite{Edits: []dsl.Edit{
			{Within: "_root", Token: "var", ReplaceWith: "let"},
		}},
	}
	f := ForRule(rule)
	if !f.Empty() {
		t.Fatalf("within-only rewrite must leave filter empty, got %+v", f)
	}
	if !MayMatch([]byte("const x = 1"), []Filter{f}) {
		t.Fatal("diagnose-capable rule without substring constraints must MayMatch")
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

func TestForRule_multipleMatchesNotInferred(t *testing.T) {
	rule := &dsl.Rule{
		Match: dsl.Pattern{
			Where: []dsl.Predicate{
				{Op: "matches", Args: []dsl.Arg{{Str: "@a"}, {Str: "foo|bar"}}},
				{Op: "matches", Args: []dsl.Arg{{Str: "@b"}, {Str: "baz"}}},
			},
		},
	}
	f := ForRule(rule)
	if len(f.AnyOf) != 0 {
		t.Fatalf("multiple matches must not collapse into AnyOf, got %v", f.AnyOf)
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

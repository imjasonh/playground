package match

import (
	"testing"

	"github.com/odvcencio/gotreesitter/grammars"

	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/tsutil"
)

func TestNodeIsAndNodeIsNot(t *testing.T) {
	src := []byte("const a = Object.assign({}, src);\nconst b = Object.assign({}, ...xs);\n")
	tree, root, err := tsutil.Parse(t.Context(), grammars.JavascriptLanguage(), src, "")
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()

	env := &Env{Predicates: DefaultRegistry()}
	patAllow := &dsl.Pattern{
		Node: []string{"call_expression"},
		Fields: map[string]dsl.Child{
			"arguments": {
				Pattern: &dsl.Pattern{
					Node: []string{"arguments"},
					Children: []dsl.Child{
						{},
						{Capture: "src"},
					},
				},
			},
		},
		Where: []dsl.Predicate{
			{Op: "node_is_not", Args: []dsl.Arg{{Str: "@src"}, {Str: "spread_element"}}},
		},
	}
	got := FindAll(patAllow, root, env)
	if len(got) != 1 {
		t.Fatalf("node_is_not spread: got %d matches, want 1", len(got))
	}

	patSpread := &dsl.Pattern{
		Node: []string{"call_expression"},
		Fields: map[string]dsl.Child{
			"arguments": {
				Pattern: &dsl.Pattern{
					Node: []string{"arguments"},
					Children: []dsl.Child{
						{},
						{Capture: "src"},
					},
				},
			},
		},
		Where: []dsl.Predicate{
			{Op: "node_is", Args: []dsl.Arg{{Str: "@src"}, {Str: "spread_element"}}},
		},
	}
	got = FindAll(patSpread, root, env)
	if len(got) != 1 {
		t.Fatalf("node_is spread: got %d matches, want 1", len(got))
	}
}

func TestSubtreeLacks(t *testing.T) {
	src := []byte("type A = Array<number>;\ntype B = Array<Array<number>>;\n")
	tree, root, err := tsutil.Parse(t.Context(), grammars.TypescriptLanguage(), src, "")
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()

	env := &Env{Predicates: DefaultRegistry()}
	// Match generic_type named Array whose type_arguments lack nested generic_type.
	pat := &dsl.Pattern{
		Node: []string{"generic_type"},
		Fields: map[string]dsl.Child{
			"name": {Capture: "outer", Pattern: &dsl.Pattern{Node: []string{"type_identifier"}}},
			"type_arguments": {
				Capture: "args",
				Pattern: &dsl.Pattern{Node: []string{"type_arguments"}},
			},
		},
		Where: []dsl.Predicate{
			{Op: "eq", Args: []dsl.Arg{{Str: "@outer"}, {Str: "Array"}}},
			{Op: "subtree_lacks", Args: []dsl.Arg{{Str: "@args"}, {Str: "generic_type"}}},
		},
	}
	got := FindAll(pat, root, env)
	// Leaf Arrays: top-level `Array<number>` and the inner `Array<number>`
	// inside `Array<Array<number>>`. The outer nested Array is excluded.
	if len(got) != 2 {
		t.Fatalf("subtree_lacks: got %d matches, want 2 leaf Arrays", len(got))
	}
}

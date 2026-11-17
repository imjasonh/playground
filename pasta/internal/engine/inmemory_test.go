package engine

import (
	"fmt"
	"math"
	"reflect"
	"strings"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/effect"
	"github.com/imjasonh/playground/pasta/internal/lang"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// chainFiles returns n Go files where file i assigns x{i+1} to x{i}
// and passes x{i} to sink. The last file assigns seed to x{n-1}, so a
// fact on x{n-1} reaches x0 only after n-1 propagation steps that each
// cross a file boundary, in the reverse of input order.
func chainFiles(t *testing.T, n int) []FileInput {
	t.Helper()
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	var files []FileInput
	for i := range n {
		rhs := fmt.Sprintf("x%d", i+1)
		if i == n-1 {
			rhs = "seed"
		}
		src := fmt.Sprintf("package p\n\nfunc f%d() {\n\tx%d = %s\n\tsink(x%d)\n}\n", i, i, rhs, i)
		files = append(files, FileInput{FileID: fmt.Sprintf("f%d.go", i), Src: []byte(src), Lang: goLang})
	}
	return files
}

// assignRule matches `lhs = rhs` between two identifiers.
func assignRule(name string, where []dsl.Predicate, provides, requires []string) dsl.Rule {
	ident := &dsl.Pattern{Node: []string{"identifier"}}
	return dsl.Rule{
		Name:      name,
		Languages: []string{"go"},
		Provides:  provides,
		Requires:  requires,
		Match: dsl.Pattern{
			Node: []string{"assignment_statement"},
			Fields: map[string]dsl.Child{
				"left":  {Node: []string{"expression_list"}, Children: []dsl.Child{{Capture: "lhs", Pattern: ident}}},
				"right": {Node: []string{"expression_list"}, Children: []dsl.Child{{Capture: "rhs", Pattern: ident}}},
			},
			Where: where,
		},
		Emit: []dsl.EmitFact{{Fact: "k", Attach: "lhs"}},
	}
}

// sinkRule reports sink(x) when x has the fact k.
func sinkRule() dsl.Rule {
	return dsl.Rule{
		Name:      "sink",
		Languages: []string{"go"},
		Requires:  []string{"k"},
		Match: dsl.Pattern{
			Node: []string{"call_expression"},
			Fields: map[string]dsl.Child{
				"function":  {Capture: "fn", Pattern: &dsl.Pattern{Node: []string{"identifier"}}},
				"arguments": {Node: []string{"argument_list"}, Children: []dsl.Child{{Capture: "arg", Pattern: &dsl.Pattern{Node: []string{"identifier"}}}}},
			},
			Where: []dsl.Predicate{
				{Op: "eq", Args: []dsl.Arg{{Str: "@fn"}, {Str: "sink"}}},
				{Op: "has_fact", Args: []dsl.Arg{{Str: "@arg"}, {Str: "k"}}},
			},
		},
		Diagnose: &dsl.Diagnostic{Message: "@arg reaches sink"},
	}
}

func chainAnalyzer(propagate dsl.Rule) *dsl.Analyzer {
	return &dsl.Analyzer{Name: "chain", Rules: map[string]dsl.Rule{
		"seed":      assignRule("seed", []dsl.Predicate{{Op: "eq", Args: []dsl.Arg{{Str: "@rhs"}, {Str: "seed"}}}}, []string{"k"}, nil),
		"propagate": propagate,
		"sink":      sinkRule(),
	}}
}

func diagnosticsByFile(results []Result) [][]string {
	out := make([][]string, len(results))
	for i, r := range results {
		for _, d := range r.Diagnostics {
			out[i] = append(out[i], d.Rule+": "+d.Message)
		}
	}
	return out
}

// TestInMemoryTreeBudgetReparses runs a multi-step cross-file fixpoint
// with every tree kept and with no tree kept. The second run parses
// files again for later passes and must report the same diagnostics.
func TestInMemoryTreeBudgetReparses(t *testing.T) {
	const n = 8
	files := chainFiles(t, n)
	a := chainAnalyzer(assignRule("propagate",
		[]dsl.Predicate{{Op: "has_fact", Args: []dsl.Arg{{Str: "@rhs"}, {Str: "k"}}}},
		[]string{"k"}, []string{"k"}))

	var keptStats Stats
	kept, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a}, WithTreeBudget(0), WithStats(&keptStats))
	if err != nil {
		t.Fatal(err)
	}
	if got := keptStats.Reparsed.Load(); got != 0 {
		t.Errorf("unlimited tree budget reparsed %d files, want 0", got)
	}
	got := diagnosticsByFile(kept)
	for i := range n {
		want := []string{fmt.Sprintf("sink: x%d reaches sink", i)}
		if !reflect.DeepEqual(got[i], want) {
			t.Errorf("file %d diagnostics = %v, want %v", i, got[i], want)
		}
	}

	var spillStats Stats
	spilled, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a}, WithTreeBudget(1), WithStats(&spillStats))
	if err != nil {
		t.Fatal(err)
	}
	if spillStats.Reparsed.Load() == 0 {
		t.Error("one-byte tree budget reparsed no files")
	}
	if s := diagnosticsByFile(spilled); !reflect.DeepEqual(s, got) {
		t.Errorf("diagnostics with released trees = %v, want %v", s, got)
	}
}

// TestInMemoryTreeBudgetRebuildsCompactTrees pads the chain's files
// and gives it a tree budget too small for any Go tree, but whose second half holds every
// compact tree. Later passes must rebuild trees from those instead of
// parsing the files again, and report the same diagnostics.
func TestInMemoryTreeBudgetRebuildsCompactTrees(t *testing.T) {
	const n = 8
	files := chainFiles(t, n)
	a := chainAnalyzer(assignRule("propagate",
		[]dsl.Predicate{{Op: "has_fact", Args: []dsl.Arg{{Str: "@rhs"}, {Str: "k"}}}},
		[]string{"k"}, []string{"k"}))

	pad := "\nfunc g() {\n" + strings.Repeat("\tg(1, 2)\n", 50) + "}\n"
	var compactBytes int64
	minNodes := math.MaxInt
	for i := range files {
		f := &files[i]
		f.Src = append(f.Src, pad...)
		tree, _, err := tsutil.Parse(t.Context(), f.Lang.GetLanguage(), f.Src, f.FileID)
		if err != nil {
			t.Fatal(err)
		}
		compactBytes += int64(len(tree.Compact()))
		minNodes = min(minNodes, tree.NodeCount())
	}
	budget := 2 * compactBytes
	if budget >= int64(minNodes)*treeBytesPerNode {
		t.Fatalf("budget %d holds a Go tree of %d nodes", budget, minNodes)
	}

	want, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a}, WithTreeBudget(0))
	if err != nil {
		t.Fatal(err)
	}
	var stats Stats
	got, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a}, WithTreeBudget(budget), WithStats(&stats))
	if err != nil {
		t.Fatal(err)
	}
	if r := stats.Reparsed.Load(); r != 0 {
		t.Errorf("reparsed %d files, want 0", r)
	}
	if stats.Rebuilt.Load() == 0 {
		t.Error("rebuilt no trees")
	}
	if g, w := diagnosticsByFile(got), diagnosticsByFile(want); !reflect.DeepEqual(g, w) {
		t.Errorf("diagnostics with compact trees = %v, want %v", g, w)
	}
}

// TestInMemoryNotHasFactIteratesInOrder runs a fixpoint group whose
// rule emits k on x{i} only while x{i+1} has no k. Which facts exist
// at the end depends on the order the files are visited. The seed rule
// gives x{n-1} k before the group runs, so x{n-2} never gets it. In
// input order, every other file runs before the one that would give
// its rhs k, so each of those x{i} gets k and its sink reports, as in
// a serial run.
func TestInMemoryNotHasFactIteratesInOrder(t *testing.T) {
	const n = 16
	files := chainFiles(t, n)
	a := chainAnalyzer(assignRule("propagate",
		[]dsl.Predicate{{Op: "not_has_fact", Args: []dsl.Arg{{Str: "@rhs"}, {Str: "k"}}}},
		[]string{"k"}, []string{"k"}))
	for _, budget := range []int64{0, 1} {
		results, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a}, WithTreeBudget(budget))
		if err != nil {
			t.Fatal(err)
		}
		got := diagnosticsByFile(results)
		for i := range n {
			want := []string{fmt.Sprintf("sink: x%d reaches sink", i)}
			if i == n-2 {
				want = nil
			}
			if !reflect.DeepEqual(got[i], want) {
				t.Errorf("budget %d: file %d diagnostics = %v, want %v", budget, i, got[i], want)
			}
		}
	}
}

func TestSetGroupOutput(t *testing.T) {
	diag := func(msg string) Result {
		return Result{Diagnostics: []effect.Diagnostic{{Message: msg}}}
	}
	var outs []groupOutput
	outs = setGroupOutput(outs, 2, diag("first"))
	outs = setGroupOutput(outs, 5, diag("other"))
	outs = setGroupOutput(outs, 2, diag("second"))
	if len(outs) != 2 {
		t.Fatalf("got %d outputs, want 2: %+v", len(outs), outs)
	}
	for _, o := range outs {
		if o.group == 2 && o.diagnostics[0].Message != "second" {
			t.Errorf("group 2 output = %q, want the replacement", o.diagnostics[0].Message)
		}
	}
	outs = setGroupOutput(outs, 5, Result{})
	if len(outs) != 1 || outs[0].group != 2 {
		t.Errorf("an empty result left %+v, want only group 2", outs)
	}
}

package engine

import (
	"fmt"
	"reflect"
	"sort"
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/lang"
)

func TestGroupLevels(t *testing.T) {
	rule := func(provides, requires []string) dsl.Rule {
		return dsl.Rule{Provides: provides, Requires: requires}
	}
	a := &dsl.Analyzer{Name: "t", Rules: map[string]dsl.Rule{
		"source":    rule([]string{"tainted"}, nil),
		"propagate": rule([]string{"tainted"}, []string{"tainted"}),
		"sink":      rule(nil, []string{"tainted"}),
		"alone":     rule(nil, nil),
		"orphan":    rule(nil, []string{"unprovided"}),
	}}
	groups, err := scheduleGroups([]*dsl.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	levels := groupLevels(groups)
	got := map[string]int{}
	for level, idxs := range levels {
		if !sort.IntsAreSorted(idxs) {
			t.Errorf("level %d groups %v are not in schedule order", level, idxs)
		}
		for _, gi := range idxs {
			for _, sr := range groups[gi].rules {
				got[sr.name] = level
			}
		}
	}
	want := map[string]int{"source": 0, "alone": 0, "orphan": 0, "propagate": 1, "sink": 2}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("levels = %v, want %v", got, want)
	}
}

// TestInMemoryKeepsScheduleOrder runs a consumer rule that the schedule
// places between two independent rules. The in-memory path runs the
// consumer a level later, so each file's diagnostics must be put back
// in schedule order.
func TestInMemoryKeepsScheduleOrder(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	rule := func(name string, provides, requires []string) dsl.Rule {
		return dsl.Rule{
			Name:      name,
			Languages: []string{goLang.Name},
			Match:     dsl.Pattern{Node: []string{"source_file"}},
			Diagnose:  &dsl.Diagnostic{Message: name},
			Provides:  provides,
			Requires:  requires,
		}
	}
	a := &dsl.Analyzer{Name: "t", Rules: map[string]dsl.Rule{
		"a_alone":    rule("a_alone", nil, nil),
		"b_consumer": rule("b_consumer", nil, []string{"f"}),
		"z_provider": rule("z_provider", []string{"f"}, nil),
	}}
	groups, err := scheduleGroups([]*dsl.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	var want []string
	for _, g := range groups {
		want = append(want, g.rules[0].name)
	}
	if !reflect.DeepEqual(want, []string{"z_provider", "b_consumer", "a_alone"}) {
		t.Fatalf("schedule order %v no longer puts the consumer between level-0 rules; rework the test", want)
	}

	var files []FileInput
	for i := range 16 {
		files = append(files, FileInput{FileID: fmt.Sprintf("f%d.go", i), Src: []byte("package p\n"), Lang: goLang})
	}
	results, err := RunGroup(t.Context(), files, []*dsl.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	for i, r := range results {
		var got []string
		for _, d := range r.Diagnostics {
			got = append(got, d.Rule)
		}
		if !reflect.DeepEqual(got, want) {
			t.Errorf("file %d diagnostics %v, want schedule order %v", i, got, want)
		}
	}
}

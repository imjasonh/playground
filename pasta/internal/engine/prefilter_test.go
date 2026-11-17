package engine

import (
	"testing"
	"time"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/lang"
)

func TestStreamingPrefilterSkipsParse(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	// A rule that can only fire when the literal "UNIQ_TOKEN_ZZZ" is
	// present — the clean file below must be prefilter-skipped.
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:             "r",
				Languages:        []string{goLang.Name},
				RequireSubstring: []string{"UNIQ_TOKEN_ZZZ"},
				Match:            dsl.Pattern{Node: []string{"source_file"}},
				Diagnose:         &dsl.Diagnostic{Message: "should not fire"},
			},
		},
	}
	src := []byte("package p\n\nfunc F() {}\n")
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a}, WithParseTimeout(2*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 {
		t.Fatalf("len=%d", len(results))
	}
	if len(results[0].Diagnostics) != 0 {
		t.Fatalf("prefilter should skip; got %v", results[0].Diagnostics)
	}
}

func TestStreamingPrefilterAllowsHit(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:             "r",
				Languages:        []string{goLang.Name},
				RequireSubstring: []string{"UNIQ_TOKEN_ZZZ"},
				Match:            dsl.Pattern{Node: []string{"source_file"}},
				Diagnose:         &dsl.Diagnostic{Message: "hit"},
			},
		},
	}
	src := []byte("package p\n\n// UNIQ_TOKEN_ZZZ\nfunc F() {}\n")
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	if len(results[0].Diagnostics) != 1 {
		t.Fatalf("want 1 diagnostic, got %v", results[0].Diagnostics)
	}
}

// TestPrefilterSkipsRule runs a file that one rule's filter rejects and
// another rule matches, on the streaming path and, with a rule that
// requires a fact, on the in-memory path. Only the unfiltered rule
// fires.
func TestPrefilterSkipsRule(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	for name, requires := range map[string][]string{"streaming": nil, "in-memory": {"f"}} {
		t.Run(name, func(t *testing.T) {
			a := &dsl.Analyzer{
				Name: "t",
				Rules: map[string]dsl.Rule{
					"filtered": {
						Name:             "filtered",
						Languages:        []string{goLang.Name},
						RequireSubstring: []string{"UNIQ_TOKEN_ZZZ"},
						Match:            dsl.Pattern{Node: []string{"source_file"}},
						Diagnose:         &dsl.Diagnostic{Message: "should not fire"},
					},
					"unfiltered": {
						Name:      "unfiltered",
						Languages: []string{goLang.Name},
						Requires:  requires,
						Match:     dsl.Pattern{Node: []string{"source_file"}},
						Diagnose:  &dsl.Diagnostic{Message: "hit"},
					},
				},
			}
			results, err := RunGroup(t.Context(), []FileInput{
				{FileID: "a.go", Src: []byte("package p\n"), Lang: goLang},
			}, []*dsl.Analyzer{a})
			if err != nil {
				t.Fatal(err)
			}
			d := results[0].Diagnostics
			if len(d) != 1 || d[0].Rule != "unfiltered" {
				t.Fatalf("want one diagnostic from unfiltered, got %+v", d)
			}
		})
	}
}

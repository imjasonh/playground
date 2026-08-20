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

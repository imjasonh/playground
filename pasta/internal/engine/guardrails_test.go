package engine

import (
	"context"
	"testing"
	"time"

	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/lang"
)

func TestStreamingParseErrorsSkip(t *testing.T) {
	js, ok := lang.ByExt(".js")
	if !ok {
		t.Fatal("js language not registered")
	}
	// Broken source — tree-sitter still returns a tree, but HasError.
	src := []byte("const x = {{{{")
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:      "r",
				Languages: []string{js.Name},
				Match:     dsl.Pattern{Node: []string{"program", "source_file"}},
				Diagnose:  &dsl.Diagnostic{Message: "should not fire on ERROR tree"},
			},
		},
	}
	var stats Stats
	results, err := RunGroup(context.Background(), []FileInput{
		{FileID: "bad.js", Src: src, Lang: js},
	}, []*dsl.Analyzer{a}, WithStats(&stats), WithParseTimeout(2*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if results[0].SkipReason != "parse errors" {
		t.Fatalf("SkipReason=%q, want parse errors", results[0].SkipReason)
	}
	if len(results[0].Diagnostics) != 0 {
		t.Fatalf("ERROR skip must not diagnose, got %v", results[0].Diagnostics)
	}
	if stats.ParseErrors.Load() != 1 {
		t.Fatalf("ParseErrors=%d, want 1", stats.ParseErrors.Load())
	}
	if stats.Parsed.Load() != 0 {
		t.Fatalf("Parsed=%d, want 0", stats.Parsed.Load())
	}
}

func TestStreamingMemoryBudgetSkips(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	src := []byte("package p\n\nfunc F() {}\n")
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:             "r",
				Languages:        []string{goLang.Name},
				RequireSubstring: []string{"package"},
				Match:            dsl.Pattern{Node: []string{"source_file"}},
				Diagnose:         &dsl.Diagnostic{Message: "hit"},
			},
		},
	}
	var stats Stats
	results, err := RunGroup(context.Background(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
		{FileID: "b.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a},
		WithMemoryBudget(int64(len(src))),
		WithStats(&stats),
	)
	if err != nil {
		t.Fatal(err)
	}
	var parsed, memSkip int
	for _, r := range results {
		switch r.SkipReason {
		case "":
			parsed++
			if len(r.Diagnostics) != 1 {
				t.Fatalf("parsed file diags=%v", r.Diagnostics)
			}
		case "memory budget exceeded":
			memSkip++
		default:
			t.Fatalf("unexpected skip %q", r.SkipReason)
		}
	}
	if parsed != 1 || memSkip != 1 {
		t.Fatalf("parsed=%d memSkip=%d stats=%+v", parsed, memSkip, stats.Snapshot())
	}
	if stats.MemorySkipped.Load() != 1 {
		t.Fatalf("MemorySkipped=%d", stats.MemorySkipped.Load())
	}
}

func TestStreamingPrefilterStats(t *testing.T) {
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
	var stats Stats
	_, err := RunGroup(context.Background(), []FileInput{
		{FileID: "a.go", Src: []byte("package p\n"), Lang: goLang},
	}, []*dsl.Analyzer{a}, WithStats(&stats))
	if err != nil {
		t.Fatal(err)
	}
	if stats.Walked.Load() != 1 || stats.PrefilterSkipped.Load() != 1 {
		t.Fatalf("stats=%+v", stats.Snapshot())
	}
}

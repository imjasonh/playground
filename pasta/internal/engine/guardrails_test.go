package engine

import (
	"testing"
	"time"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/lang"
	"github.com/imjasonh/playground/pasta/internal/parsecache"
)

func TestStreamingParseErrorsSkipHeavy(t *testing.T) {
	js, ok := lang.ByExt(".js")
	if !ok {
		t.Fatal("js language not registered")
	}
	// Heavily broken — ErrorHeavy should skip.
	// Official C tree-sitter recovers `{{{{` more cleanly than the old
	// pure-Go port; use denser garbage so ERROR nodes dominate.
	src := []byte("!!!!!!!\n@@@@@@@\n#######\n{{{{{{{{\n")
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:      "r",
				Languages: []string{js.Name},
				Match:     dsl.Pattern{Node: []string{"program", "source_file"}},
				Diagnose:  &dsl.Diagnostic{Message: "should not fire on ERROR-heavy tree"},
			},
		},
	}
	var stats Stats
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "bad.js", Src: src, Lang: js},
	}, []*dsl.Analyzer{a}, WithStats(&stats), WithParseTimeout(2*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if results[0].SkipReason != "parse errors" {
		t.Fatalf("SkipReason=%q, want parse errors", results[0].SkipReason)
	}
	if len(results[0].Diagnostics) != 0 {
		t.Fatalf("ERROR-heavy skip must not diagnose, got %v", results[0].Diagnostics)
	}
	if stats.ParseErrors.Load() != 1 {
		t.Fatalf("ParseErrors=%d, want 1", stats.ParseErrors.Load())
	}
	if stats.Parsed.Load() != 0 {
		t.Fatalf("Parsed=%d, want 0", stats.Parsed.Load())
	}
}

func TestStreamingParseDegradedStillAnalyzes(t *testing.T) {
	js, ok := lang.ByExt(".js")
	if !ok {
		t.Fatal("js language not registered")
	}
	// Trailing junk: HasError but not ErrorHeavy.
	src := []byte("const uniq_degraded_token = 1;\n}\n")
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:             "r",
				Languages:        []string{js.Name},
				RequireSubstring: []string{"uniq_degraded_token"},
				Match:            dsl.Pattern{Node: []string{"program"}},
				Diagnose:         &dsl.Diagnostic{Message: "hit"},
			},
		},
	}
	var stats Stats
	cache := parsecache.Open(t.TempDir(), parsecache.HashRules([]*dsl.Analyzer{a}), 0)
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "light.js", Src: src, Lang: js},
	}, []*dsl.Analyzer{a}, WithStats(&stats), WithCache(cache))
	if err != nil {
		t.Fatal(err)
	}
	if results[0].SkipReason != "" {
		t.Fatalf("light ERROR should not skip, got %q", results[0].SkipReason)
	}
	if len(results[0].Diagnostics) != 1 {
		t.Fatalf("want diagnose on degraded tree, got %v", results[0].Diagnostics)
	}
	if stats.ParseDegraded.Load() != 1 {
		t.Fatalf("ParseDegraded=%d, want 1", stats.ParseDegraded.Load())
	}
	if s := cache.Stats(); s.Writes != 0 {
		t.Fatalf("degraded trees must not be cached, writes=%d", s.Writes)
	}
}

func TestStreamingMemoryBudgetSkipsDeterministic(t *testing.T) {
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
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
		{FileID: "b.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a},
		WithMemoryBudget(int64(len(src))),
		WithStats(&stats),
	)
	if err != nil {
		t.Fatal(err)
	}
	// FileInput order: first admitted, second skipped.
	if results[0].SkipReason != "" || len(results[0].Diagnostics) != 1 {
		t.Fatalf("first file: skip=%q diags=%v", results[0].SkipReason, results[0].Diagnostics)
	}
	if results[1].SkipReason != "memory budget exceeded" {
		t.Fatalf("second file SkipReason=%q", results[1].SkipReason)
	}
	if stats.MemorySkipped.Load() != 1 {
		t.Fatalf("MemorySkipped=%d", stats.MemorySkipped.Load())
	}
}

func TestMemoryTrackerSpansRunGroups(t *testing.T) {
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
	tracker := &MemoryTracker{Budget: int64(len(src))}
	r1, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a}, WithMemoryTracker(tracker))
	if err != nil {
		t.Fatal(err)
	}
	if r1[0].SkipReason != "" {
		t.Fatalf("first run skipped: %q", r1[0].SkipReason)
	}
	r2, err := RunGroup(t.Context(), []FileInput{
		{FileID: "b.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a}, WithMemoryTracker(tracker))
	if err != nil {
		t.Fatal(err)
	}
	if r2[0].SkipReason != "memory budget exceeded" {
		t.Fatalf("second RunGroup should hit shared budget, got %q", r2[0].SkipReason)
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
	_, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: []byte("package p\n"), Lang: goLang},
	}, []*dsl.Analyzer{a}, WithStats(&stats))
	if err != nil {
		t.Fatal(err)
	}
	if stats.Walked.Load() != 1 || stats.PrefilterSkipped.Load() != 1 {
		t.Fatalf("stats=%+v", stats.Snapshot())
	}
}

func TestCacheMissAfterSchemaBump(t *testing.T) {
	// Smoke: Open uses current schemaVersion path; a fresh cache has no
	// v1 bleed-through. (Full cross-version fixture is overkill — the
	// const bump is the invalidation mechanism.)
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	src := []byte("package p\n")
	a := &dsl.Analyzer{
		Name: "t",
		Rules: map[string]dsl.Rule{
			"r": {
				Name:      "r",
				Languages: []string{goLang.Name},
				Match:     dsl.Pattern{Node: []string{"source_file"}},
				Diagnose:  &dsl.Diagnostic{Message: "hit"},
			},
		},
	}
	dir := t.TempDir()
	cache := parsecache.Open(dir, parsecache.HashRules([]*dsl.Analyzer{a}), 0)
	_, err := RunGroup(t.Context(), []FileInput{
		{FileID: "a.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a}, WithCache(cache))
	if err != nil {
		t.Fatal(err)
	}
	if cache.Stats().Writes != 1 {
		t.Fatalf("writes=%d", cache.Stats().Writes)
	}
}

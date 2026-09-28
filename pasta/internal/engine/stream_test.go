package engine

import (
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/lang"
)

// TestStreamingReadsPathLazily ensures FileInput with Path set and Src
// nil is readable inside the worker — the CLI's multi-GB RSS fix.
func TestStreamingReadsPathLazily(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	dir := t.TempDir()
	path := filepath.Join(dir, "a.go")
	src := []byte("package p\n\nfunc F() {\n\tif true {\n\t} else {\n\t}\n}\n")
	if err := os.WriteFile(path, src, 0o644); err != nil {
		t.Fatal(err)
	}

	analyzer := &dsl.Analyzer{
		Name: "go_empty_else",
		Rules: map[string]dsl.Rule{
			"empty_else": {
				Name:      "empty_else",
				Languages: []string{"go"},
				Match: dsl.Pattern{
					Node: []string{"if_statement"},
					Fields: map[string]dsl.Child{
						"alternative": {
							Capture: "alt",
							Pattern: &dsl.Pattern{Node: []string{"block"}},
						},
					},
					Where: []dsl.Predicate{
						{Op: "empty", Args: []dsl.Arg{{Str: "@alt"}}},
					},
				},
				Diagnose: &dsl.Diagnostic{Message: "empty else", Severity: dsl.SeverityHint},
			},
		},
	}

	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: path, Path: path, Lang: goLang}, // Src intentionally nil
	}, []*dsl.Analyzer{analyzer}, WithParseTimeout(2*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 || len(results[0].Diagnostics) == 0 {
		t.Fatalf("expected diagnostic from path-only input, got %+v", results)
	}
}

// TestRunGroupSkipsFileRemovedBeforeRead covers a path-only input whose
// file is gone when the engine reads it, as when another process deletes
// a scratch file after the CLI walk listed it. Both execution paths skip
// the file and analyze the rest. The memory budget makes the in-memory
// path wait on every earlier file's admission turn.
func TestRunGroupSkipsFileRemovedBeforeRead(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	dir := t.TempDir()
	removed := filepath.Join(dir, "removed.go")
	kept := filepath.Join(dir, "kept.go")
	if err := os.WriteFile(kept, []byte("package p\n"), 0o644); err != nil {
		t.Fatal(err)
	}

	streaming := dsl.Rule{
		Name:      "r",
		Languages: []string{goLang.Name},
		Match:     dsl.Pattern{Node: []string{"source_file"}},
		Diagnose:  &dsl.Diagnostic{Message: "hit"},
	}
	inMemory := streaming
	inMemory.Requires = []string{"unprovided"}
	for name, rule := range map[string]dsl.Rule{"streaming": streaming, "in-memory": inMemory} {
		t.Run(name, func(t *testing.T) {
			a := &dsl.Analyzer{Name: "t", Rules: map[string]dsl.Rule{"r": rule}}
			results, err := RunGroup(t.Context(), []FileInput{
				{FileID: removed, Path: removed, Lang: goLang},
				{FileID: kept, Path: kept, Lang: goLang},
			}, []*dsl.Analyzer{a}, WithMemoryBudget(1<<20))
			if err != nil {
				t.Fatal(err)
			}
			if results[0].SkipReason != "file not found" {
				t.Errorf("removed file: SkipReason=%q, want %q", results[0].SkipReason, "file not found")
			}
			if results[1].SkipReason != "" || len(results[1].Diagnostics) != 1 {
				t.Errorf("kept file: skip=%q diags=%v", results[1].SkipReason, results[1].Diagnostics)
			}
		})
	}
}

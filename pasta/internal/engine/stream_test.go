package engine

import (
	"context"
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

	results, err := RunGroup(context.Background(), []FileInput{
		{FileID: path, Path: path, Lang: goLang}, // Src intentionally nil
	}, []*dsl.Analyzer{analyzer}, WithParseTimeout(2*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 || len(results[0].Diagnostics) == 0 {
		t.Fatalf("expected diagnostic from path-only input, got %+v", results)
	}
}

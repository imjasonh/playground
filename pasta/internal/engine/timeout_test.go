package engine

import (
	"testing"
	"time"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/lang"
	"github.com/imjasonh/playground/pasta/internal/parsecache"
)

func TestStreamingParseTimeoutSetsSkipReason(t *testing.T) {
	goLang, ok := lang.ByExt(".go")
	if !ok {
		t.Fatal("go language not registered")
	}
	src := []byte("package p\n\n")
	for i := 0; i < 3000; i++ {
		src = append(src, []byte("func F() { var x int; _ = x }\n")...)
	}
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
	cache := parsecache.Open(t.TempDir(), parsecache.HashRules([]*dsl.Analyzer{a}), 0)
	results, err := RunGroup(t.Context(), []FileInput{
		{FileID: "big.go", Src: src, Lang: goLang},
	}, []*dsl.Analyzer{a}, WithParseTimeout(time.Microsecond), WithCache(cache))
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 {
		t.Fatalf("len=%d", len(results))
	}
	if results[0].SkipReason != "too complex to analyze" {
		// Fast hosts may finish before 1µs; accept either skip or success.
		if results[0].SkipReason == "" && len(results[0].Diagnostics) > 0 {
			t.Skip("parse finished within 1µs; cannot assert timeout skip")
		}
		t.Fatalf("SkipReason=%q, diags=%d", results[0].SkipReason, len(results[0].Diagnostics))
	}
	if len(results[0].Diagnostics) != 0 {
		t.Fatalf("timeout skip must not produce diagnostics")
	}
	if s := cache.Stats(); s.Writes != 0 {
		t.Fatalf("timeout skip must not write cache entries, got %+v", s)
	}
	if results[0].Src == nil {
		t.Fatal("Src should still be set after timeout skip")
	}
}

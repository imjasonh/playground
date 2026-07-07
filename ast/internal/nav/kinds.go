// Package nav builds language-agnostic navigation features on top of the core
// engine and the curated tree-sitter query files: normalized "kind" selectors
// (from tags.scm / highlights.scm) and scope-aware rename (from locals.scm).
//
// These features are inspired by LSP, which standardizes a cross-language
// symbol taxonomy (SymbolKind) and semantic, scope-aware rename while leaving
// the actual matching to each server. Here the taxonomy is realized by mapping
// tree-sitter capture names to a small normalized vocabulary, and scope-aware
// rename is realized by resolving references against definitions using the
// standard tree-sitter locals model.
package nav

import (
	"context"
	"fmt"
	"sort"
	"strings"

	"github.com/imjasonh/playground/ast/internal/engine"
	"github.com/imjasonh/playground/ast/internal/langs"
)

// tagKinds maps tags.scm capture names to normalized structural kinds.
var tagKinds = map[string]string{
	"definition.function":  "function",
	"definition.method":    "method",
	"definition.class":     "class",
	"definition.struct":    "struct",
	"definition.interface": "interface",
	"definition.enum":      "enum",
	"definition.type":      "type",
	"definition.constant":  "constant",
	"definition.variable":  "variable",
	"definition.field":     "field",
	"definition.module":    "module",
	"definition.import":    "import",
	"reference.call":       "call",
}

// highlightKinds maps highlights.scm capture names to normalized token kinds.
var highlightKinds = map[string]string{
	"comment":            "comment",
	"string":             "string",
	"number":             "number",
	"keyword":            "keyword",
	"variable.parameter": "parameter",
}

// AllKinds returns the full normalized kind vocabulary, sorted.
func AllKinds() []string {
	set := map[string]bool{}
	for _, k := range tagKinds {
		set[k] = true
	}
	for _, k := range highlightKinds {
		set[k] = true
	}
	out := make([]string, 0, len(set))
	for k := range set {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// IsKind reports whether name is part of the normalized vocabulary.
func IsKind(name string) bool {
	for _, k := range AllKinds() {
		if k == name {
			return true
		}
	}
	return false
}

// queryFileForKind returns which curated query file ("tags" or "highlights")
// produces the given normalized kind.
func queryFileForKind(kind string) string {
	for _, k := range highlightKinds {
		if k == kind {
			return langs.QueryHighlights
		}
	}
	return langs.QueryTags
}

// KindHit is one node selected by a --kind query.
type KindHit struct {
	Kind    string
	Capture engine.Capture
}

// SelectKinds finds all nodes in src whose normalized kind is one of the
// requested kinds. It runs the language's tags.scm and/or highlights.scm as
// needed. It returns an error if the language has no curated queries.
func SelectKinds(ctx context.Context, src []byte, l *langs.Language, kinds []string) ([]KindHit, error) {
	want := map[string]bool{}
	files := map[string]bool{}
	for _, k := range kinds {
		if !IsKind(k) {
			return nil, fmt.Errorf("unknown kind %q (see `ast kinds`)", k)
		}
		want[k] = true
		files[queryFileForKind(k)] = true
	}
	if len(want) == 0 {
		return nil, fmt.Errorf("no kinds requested")
	}

	var hits []KindHit
	seen := map[string]bool{}
	add := func(kind string, c engine.Capture) {
		key := fmt.Sprintf("%s:%d:%d", kind, c.StartByte, c.EndByte)
		if seen[key] {
			return
		}
		seen[key] = true
		hits = append(hits, KindHit{Kind: kind, Capture: c})
	}

	for file := range files {
		q, ok := l.LoadQuery(file)
		if !ok {
			return nil, fmt.Errorf("--kind is not available for %s (no curated queries); use -q with a tree-sitter query instead", l.Name)
		}
		matches, err := engine.Query(ctx, src, l.Sitter(), q)
		if err != nil {
			return nil, fmt.Errorf("running %s query for %s: %w", file, l.Name, err)
		}
		for _, m := range matches {
			switch file {
			case langs.QueryTags:
				kind, node, ok := tagMatchKind(m)
				if ok && want[kind] {
					add(kind, node)
				}
			case langs.QueryHighlights:
				for _, c := range m.Captures {
					if kind, ok := highlightKinds[c.Name]; ok && want[kind] {
						add(kind, c)
					}
				}
			}
		}
	}

	sort.SliceStable(hits, func(i, j int) bool {
		return hits[i].Capture.StartByte < hits[j].Capture.StartByte
	})
	return hits, nil
}

// tagMatchKind extracts the normalized kind for a tags.scm match and the node
// to report for it: the @name capture (the defined/referenced identifier) when
// present, otherwise the whole definition node.
func tagMatchKind(m engine.Match) (kind string, node engine.Capture, ok bool) {
	var name *engine.Capture
	var kindCap *engine.Capture
	var matchedKind string
	for i := range m.Captures {
		c := m.Captures[i]
		if c.Name == "name" {
			name = &m.Captures[i]
			continue
		}
		if k, isKind := tagKinds[c.Name]; isKind {
			matchedKind = k
			kindCap = &m.Captures[i]
		}
	}
	if kindCap == nil {
		return "", engine.Capture{}, false
	}
	if name != nil {
		return matchedKind, *name, true
	}
	return matchedKind, *kindCap, true
}

// KindsForLanguage returns the subset of the vocabulary that the language's
// curated queries can actually produce (by scanning capture names), sorted.
func KindsForLanguage(l *langs.Language) []string {
	set := map[string]bool{}
	if q, ok := l.LoadQuery(langs.QueryTags); ok {
		for cap, kind := range tagKinds {
			if strings.Contains(q, "@"+cap) {
				set[kind] = true
			}
		}
	}
	if q, ok := l.LoadQuery(langs.QueryHighlights); ok {
		for cap, kind := range highlightKinds {
			if strings.Contains(q, "@"+cap) {
				set[kind] = true
			}
		}
	}
	out := make([]string, 0, len(set))
	for k := range set {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

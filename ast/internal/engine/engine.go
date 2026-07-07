// Package engine contains the language-agnostic core of the ast tool: parsing
// source into a tree-sitter tree, running tree-sitter queries (the selector
// language) against it, and applying byte-range edits back to the source.
//
// Rewrites are performed as text splices at node byte ranges rather than by
// re-serializing a modified tree. tree-sitter does not losslessly print trees
// back to source, and byte-range splicing keeps every rewrite faithful to the
// original file (whitespace, comments, and formatting are untouched outside the
// edited spans). This is what makes the tool work uniformly across languages.
package engine

import (
	"context"
	"fmt"
	"sort"
	"strings"

	sitter "github.com/smacker/go-tree-sitter"
)

// Position is a 0-based row and column (in bytes) within a source file.
type Position struct {
	Row    uint32 `json:"row"`
	Column uint32 `json:"column"`
}

// Capture is a single named node captured by a query.
//
// Field is the field name under which this node sits in its parent (e.g.
// "name", "body", or "" when the node fills no named field). It is computed
// while the syntax tree is alive so consumers can reason about a node's role
// without holding a reference to the tree (whose lifetime ends when Query
// returns).
type Capture struct {
	Name      string   `json:"name"`
	Type      string   `json:"type"`
	Text      string   `json:"text"`
	Field     string   `json:"field,omitempty"`
	StartByte uint32   `json:"startByte"`
	EndByte   uint32   `json:"endByte"`
	Start     Position `json:"start"`
	End       Position `json:"end"`
}

// Match is one result of a query: the pattern that matched plus every node it
// captured.
type Match struct {
	PatternIndex int       `json:"patternIndex"`
	Captures     []Capture `json:"captures"`
}

// Capture returns the first capture with the given name (without a leading
// "@"), reporting whether one was found.
func (m Match) Capture(name string) (Capture, bool) {
	name = strings.TrimPrefix(name, "@")
	for _, c := range m.Captures {
		if c.Name == name {
			return c, true
		}
	}
	return Capture{}, false
}

// Parse parses src with the given grammar and returns the syntax tree.
func Parse(ctx context.Context, src []byte, lang *sitter.Language) (*sitter.Tree, error) {
	parser := sitter.NewParser()
	parser.SetLanguage(lang)
	tree, err := parser.ParseCtx(ctx, nil, src)
	if err != nil {
		return nil, fmt.Errorf("parsing source: %w", err)
	}
	return tree, nil
}

// Query parses src and returns every match of the tree-sitter query pattern.
// Query predicates such as #eq? and #match? are honored.
func Query(ctx context.Context, src []byte, lang *sitter.Language, pattern string) ([]Match, error) {
	q, err := sitter.NewQuery([]byte(pattern), lang)
	if err != nil {
		return nil, fmt.Errorf("invalid query: %w", err)
	}
	defer q.Close()

	if q.CaptureCount() == 0 {
		return nil, fmt.Errorf("query has no captures: add at least one capture such as @x so results reference concrete nodes")
	}

	tree, err := Parse(ctx, src, lang)
	if err != nil {
		return nil, err
	}
	defer tree.Close()

	cursor := sitter.NewQueryCursor()
	defer cursor.Close()
	cursor.Exec(q, tree.RootNode())

	var matches []Match
	for {
		m, ok := cursor.NextMatch()
		if !ok {
			break
		}
		m = cursor.FilterPredicates(m, src)
		if len(m.Captures) == 0 {
			continue
		}
		match := Match{PatternIndex: int(m.PatternIndex)}
		for _, c := range m.Captures {
			node := c.Node
			start, end := node.StartPoint(), node.EndPoint()
			match.Captures = append(match.Captures, Capture{
				Name:      q.CaptureNameForId(c.Index),
				Type:      node.Type(),
				Text:      node.Content(src),
				Field:     fieldName(node),
				StartByte: node.StartByte(),
				EndByte:   node.EndByte(),
				Start:     Position{Row: start.Row, Column: start.Column},
				End:       Position{Row: end.Row, Column: end.Column},
			})
		}
		matches = append(matches, match)
	}
	return matches, nil
}

// fieldName returns the field name under which n sits in its parent, or "".
// It must be called while the syntax tree is alive.
func fieldName(n *sitter.Node) string {
	parent := n.Parent()
	if parent == nil {
		return ""
	}
	cursor := sitter.NewTreeCursor(parent)
	defer cursor.Close()
	if !cursor.GoToFirstChild() {
		return ""
	}
	for {
		if cursor.CurrentNode().Equal(n) {
			return cursor.CurrentFieldName()
		}
		if !cursor.GoToNextSibling() {
			return ""
		}
	}
}

// Edit is a replacement of the half-open byte range [Start, End) with Text.
// A pure insertion has Start == End; a deletion has Text == "".
type Edit struct {
	Start uint32
	End   uint32
	Text  string
}

// Apply returns a copy of src with the edits applied. Edits may be supplied in
// any order; they are applied from the end of the file backwards so earlier
// byte offsets stay valid. Overlapping edits are rejected. A zero-width
// insertion is allowed to sit at the boundary of an adjacent replacement.
func Apply(src []byte, edits []Edit) ([]byte, error) {
	if len(edits) == 0 {
		return append([]byte(nil), src...), nil
	}

	ordered := make([]Edit, len(edits))
	copy(ordered, edits)
	for i, e := range ordered {
		if e.Start > e.End {
			return nil, fmt.Errorf("edit %d has start %d after end %d", i, e.Start, e.End)
		}
		if int(e.End) > len(src) {
			return nil, fmt.Errorf("edit %d end %d is past end of source (%d bytes)", i, e.End, len(src))
		}
	}

	// Sort ascending by start, then end, so overlap detection is simple and
	// insertions are applied in a stable order relative to their neighbours.
	sort.SliceStable(ordered, func(i, j int) bool {
		if ordered[i].Start != ordered[j].Start {
			return ordered[i].Start < ordered[j].Start
		}
		return ordered[i].End < ordered[j].End
	})
	for i := 1; i < len(ordered); i++ {
		prev, cur := ordered[i-1], ordered[i]
		if cur.Start < prev.End {
			return nil, fmt.Errorf("overlapping edits: [%d,%d) and [%d,%d)", prev.Start, prev.End, cur.Start, cur.End)
		}
	}

	// Reconstruct the output left-to-right from the sorted, non-overlapping
	// edits: copy the untouched span before each edit, then the replacement.
	var out []byte
	prev := uint32(0)
	for _, e := range ordered {
		out = append(out, src[prev:e.Start]...)
		out = append(out, e.Text...)
		prev = e.End
	}
	out = append(out, src[prev:]...)
	return out, nil
}

package nav

import (
	"context"
	"fmt"
	"sort"
	"strings"

	"github.com/imjasonh/playground/ast/internal/engine"
	"github.com/imjasonh/playground/ast/internal/langs"
)

// Pos is a 0-based row/column location used to target a rename.
type Pos struct {
	Row    uint32
	Column uint32
}

// scope is a lexical scope with a byte range and its parent in the scope tree.
type scope struct {
	start, end uint32
	parent     int // index into resolver.scopes, or -1 for the root
}

// resolver holds the locals model (scopes, definitions, references) for a file
// and answers binding queries against it.
type resolver struct {
	src    []byte
	scopes []scope
	defs   []engine.Capture
	refs   []engine.Capture

	// defKey[scopeIdx+"\x00"+name] is true when a definition of name has the
	// scope as its immediate enclosing scope.
	defKey map[string]bool
}

func bindingKey(scopeIdx int, name string) string {
	return fmt.Sprintf("%d\x00%s", scopeIdx, name)
}

// newResolver runs locals.scm and builds the scope tree and def/ref sets.
func newResolver(ctx context.Context, src []byte, l *langs.Language) (*resolver, error) {
	q, ok := l.LoadQuery(langs.QueryLocals)
	if !ok {
		return nil, fmt.Errorf("scope-aware rename is not available for %s (no curated locals query); use `ast rewrite` instead", l.Name)
	}
	matches, err := engine.Query(ctx, src, l.Sitter(), q)
	if err != nil {
		return nil, fmt.Errorf("running locals query for %s: %w", l.Name, err)
	}

	r := &resolver{src: src, defKey: map[string]bool{}}

	// Root scope spans the whole file.
	r.scopes = append(r.scopes, scope{start: 0, end: uint32(len(src)), parent: -1})

	// Collect scopes (deduped by range), definitions, and references.
	seenScope := map[[2]uint32]bool{}
	for _, m := range matches {
		for _, c := range m.Captures {
			switch {
			case c.Name == "local.scope":
				rng := [2]uint32{c.StartByte, c.EndByte}
				if seenScope[rng] {
					continue
				}
				seenScope[rng] = true
				r.scopes = append(r.scopes, scope{start: c.StartByte, end: c.EndByte, parent: -1})
			case strings.HasPrefix(c.Name, "local.definition"):
				r.defs = append(r.defs, c)
			case c.Name == "local.reference":
				if isMemberProperty(c) {
					continue
				}
				r.refs = append(r.refs, c)
			}
		}
	}

	r.linkScopes()
	for _, d := range r.defs {
		r.defKey[bindingKey(r.enclosingScope(d.StartByte, d.EndByte), d.Text)] = true
	}
	return r, nil
}

// linkScopes computes each scope's parent as the smallest other scope that
// strictly contains it (root contains everything).
func (r *resolver) linkScopes() {
	for i := range r.scopes {
		s := r.scopes[i]
		best := -1
		for j := range r.scopes {
			if j == i {
				continue
			}
			o := r.scopes[j]
			if o.start <= s.start && o.end >= s.end && (o.start < s.start || o.end > s.end) {
				if best == -1 || smaller(o, r.scopes[best]) {
					best = j
				}
			}
		}
		r.scopes[i].parent = best
	}
}

// smaller reports whether scope a is a tighter container than b.
func smaller(a, b scope) bool {
	if a.start != b.start {
		return a.start > b.start
	}
	return a.end < b.end
}

// enclosingScope returns the index of the smallest scope containing the byte
// range [start,end). The root scope always qualifies.
func (r *resolver) enclosingScope(start, end uint32) int {
	best := 0 // root always contains the range
	for i := 1; i < len(r.scopes); i++ {
		s := r.scopes[i]
		if s.start <= start && s.end >= end {
			if best == 0 || smaller(s, r.scopes[best]) {
				best = i
			}
		}
	}
	return best
}

// resolve returns the scope index of the binding a reference name resolves to,
// starting from the reference's enclosing scope and walking outward. It returns
// -1 when the name is free (no local definition in any enclosing scope).
func (r *resolver) resolve(name string, enclosing int) int {
	for s := enclosing; s != -1; s = r.scopes[s].parent {
		if r.defKey[bindingKey(s, name)] {
			return s
		}
	}
	return -1
}

// occurrences returns every definition and resolving reference of the binding
// identified by (scopeIdx, name), deduplicated and sorted by position.
func (r *resolver) occurrences(scopeIdx int, name string) []engine.Capture {
	var out []engine.Capture
	seen := map[[2]uint32]bool{}
	add := func(c engine.Capture) {
		key := [2]uint32{c.StartByte, c.EndByte}
		if seen[key] {
			return
		}
		seen[key] = true
		out = append(out, c)
	}
	for _, d := range r.defs {
		if d.Text == name && r.enclosingScope(d.StartByte, d.EndByte) == scopeIdx {
			add(d)
		}
	}
	for _, ref := range r.refs {
		if ref.Text != name {
			continue
		}
		if r.resolve(name, r.enclosingScope(ref.StartByte, ref.EndByte)) == scopeIdx {
			add(ref)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].StartByte < out[j].StartByte })
	return out
}

// RenameResult is the resolved set of occurrences to rename.
type RenameResult struct {
	Name        string
	Occurrences []engine.Capture
}

// RenameAt resolves the binding of the identifier at pos and returns all of its
// occurrences (definition + references) so the caller can rewrite them.
func RenameAt(ctx context.Context, src []byte, l *langs.Language, pos Pos) (*RenameResult, error) {
	r, err := newResolver(ctx, src, l)
	if err != nil {
		return nil, err
	}
	target, ok := r.identAt(pos)
	if !ok {
		return nil, fmt.Errorf("no renameable identifier at %d:%d", pos.Row+1, pos.Column+1)
	}
	scopeIdx := r.enclosingScope(target.StartByte, target.EndByte)
	if !r.defKey[bindingKey(scopeIdx, target.Text)] {
		// Not a definition here; treat as a reference and resolve it.
		scopeIdx = r.resolve(target.Text, scopeIdx)
		if scopeIdx == -1 {
			return nil, fmt.Errorf("%q at %d:%d does not resolve to a local binding (it may be a package-level, imported, or built-in symbol); use `ast rewrite` instead", target.Text, pos.Row+1, pos.Column+1)
		}
	}
	return &RenameResult{Name: target.Text, Occurrences: r.occurrences(scopeIdx, target.Text)}, nil
}

// RenameName resolves every local binding named oldName and returns all their
// occurrences. Free (non-local) uses of the name are left untouched.
func RenameName(ctx context.Context, src []byte, l *langs.Language, oldName string) (*RenameResult, error) {
	r, err := newResolver(ctx, src, l)
	if err != nil {
		return nil, err
	}
	scopeSet := map[int]bool{}
	for _, d := range r.defs {
		if d.Text == oldName {
			scopeSet[r.enclosingScope(d.StartByte, d.EndByte)] = true
		}
	}
	if len(scopeSet) == 0 {
		return nil, fmt.Errorf("no local binding named %q found; use `ast rewrite` for package-level or imported symbols", oldName)
	}
	seen := map[[2]uint32]bool{}
	var occ []engine.Capture
	for s := range scopeSet {
		for _, c := range r.occurrences(s, oldName) {
			key := [2]uint32{c.StartByte, c.EndByte}
			if seen[key] {
				continue
			}
			seen[key] = true
			occ = append(occ, c)
		}
	}
	sort.Slice(occ, func(i, j int) bool { return occ[i].StartByte < occ[j].StartByte })
	return &RenameResult{Name: oldName, Occurrences: occ}, nil
}

// identAt returns the smallest identifier (definition or reference) whose range
// contains pos.
func (r *resolver) identAt(pos Pos) (engine.Capture, bool) {
	var best engine.Capture
	found := false
	consider := func(c engine.Capture) {
		if !contains(c, pos) {
			return
		}
		if !found || (c.EndByte-c.StartByte) < (best.EndByte-best.StartByte) {
			best = c
			found = true
		}
	}
	for _, c := range r.refs {
		consider(c)
	}
	for _, c := range r.defs {
		consider(c)
	}
	return best, found
}

func contains(c engine.Capture, pos Pos) bool {
	afterStart := pos.Row > c.Start.Row || (pos.Row == c.Start.Row && pos.Column >= c.Start.Column)
	beforeEnd := pos.Row < c.End.Row || (pos.Row == c.End.Row && pos.Column < c.End.Column)
	return afterStart && beforeEnd
}

// isMemberProperty reports whether a capture is the property part of a member
// access (e.g. the `attr` in Python `obj.attr`), which must not be treated as a
// renameable local reference. Most grammars use a distinct node type for member
// properties (so they are never captured as identifiers), but Python reuses
// `identifier`, so this guard is required there and harmless elsewhere. It uses
// the node's field role within its parent, which the engine records while the
// tree is alive.
func isMemberProperty(c engine.Capture) bool {
	switch c.Field {
	case "attribute", "property", "field":
		return true
	}
	return false
}

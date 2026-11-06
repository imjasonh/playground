// Package factstore is the per-run store of facts emitted by rules and
// queried by other rules via has_fact / not_has_fact predicates.
//
// A fact is keyed by (kind, file-id, byte-range): two facts of the
// same kind on the same node de-duplicate. The file-id disambiguates
// nodes from different files in a multi-file analysis group — without
// it, two files with overlapping byte ranges would collide. When the
// anchor is an identifier-like node, the fact is ALSO indexed by
// (kind, identifier-text). The by-name index is intentionally
// file-agnostic so that a fact emitted on a function declaration in
// one file is visible at call sites in other files — that's how
// cross-file fact propagation works in pasta today.
//
// The engine also records every function and method definition it
// parses (see Define). When every fact on a name is anchored on a
// definition, a lookup by name binds to the definition nearest the
// query, the way a call binds to the function in its own file or
// package first, and the lookup succeeds only when that definition
// carries the fact. So a test helper's writeFile shadows an unrelated
// error-returning writeFile in another module. Facts anchored on other
// identifiers, such as tainted variables, keep matching by name alone.
package factstore

import (
	"cmp"
	"path"
	"strings"
	"sync"

	"github.com/imjasonh/playground/pasta/internal/testpath"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// Key identifies a fact by its kind, the file the anchor lives in,
// and the anchor's byte range within that file.
type Key struct {
	FileID    string
	StartByte uint32
	EndByte   uint32
	Kind      string
}

// NameKey identifies a fact by (identifier-text, kind). Populated as a
// secondary index whenever the emitted fact's anchor is an
// identifier-like node. Deliberately not file-scoped: looking up
// "fact F on identifier x" hits across every file in the group, which
// is what makes cross-file analysis work.
type NameKey struct {
	Name string
	Kind string
}

// Fact is a stored fact: its kind, the file + byte range of its
// anchor, and an opaque payload set by the emitting rule.
type Fact struct {
	Kind               string
	FileID             string
	StartByte, EndByte uint32
	Payload            map[string]any
}

// defKey identifies the definitions of a name in one grammar. A call
// binds only to definitions in its own language.
type defKey struct {
	Grammar string
	Name    string
}

func defKeyOf(n tsutil.Node) defKey {
	k := defKey{Name: n.Text()}
	if n.Lang != nil {
		k.Grammar = n.Lang.Grammar
	}
	return k
}

// site is the file and byte range of an identifier.
type site struct {
	FileID             string
	StartByte, EndByte uint32
}

func (f Fact) site() site { return site{f.FileID, f.StartByte, f.EndByte} }

// Store is the per-run fact store. Safe for concurrent use: the engine
// emits and queries facts from multiple worker goroutines when files
// are processed in parallel.
type Store struct {
	mu      sync.RWMutex
	byRange map[Key]Fact
	// byName holds every fact on an identifier with the given text.
	byName map[NameKey][]Fact
	// defs holds the name identifier of every definition, by grammar
	// and name.
	defs map[defKey][]site
	// isDef holds the same sites as defs, for membership tests.
	isDef map[site]bool
	// isTest caches testpath.Is by file ID.
	isTest sync.Map
}

// New returns an empty store.
func New() *Store {
	return &Store{
		byRange: map[Key]Fact{},
		byName:  map[NameKey][]Fact{},
		defs:    map[defKey][]site{},
		isDef:   map[site]bool{},
	}
}

// identifierTypes are tree-sitter node types we treat as "identifier-like"
// across grammars. Used to decide whether to populate the by-name index.
var identifierTypes = map[string]bool{
	"identifier":                    true,
	"type_identifier":               true,
	"field_identifier":              true,
	"property_identifier":           true,
	"shorthand_property_identifier": true,
}

// Define records that name, the name node of a function or method
// definition, defines its text. The engine calls it for every definition
// in a parsed file before any rule runs, so lookups by name can bind to
// the nearest definition. Definitions in files the engine skips, such as
// files no rule can match, aren't recorded.
func (s *Store) Define(name tsutil.Node) {
	if !identifierTypes[name.Type()] {
		return
	}
	st := site{name.FileID, name.StartByte(), name.EndByte()}
	k := defKeyOf(name)
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.isDef[st] {
		return
	}
	s.isDef[st] = true
	s.defs[k] = append(s.defs[k], st)
}

// Emit records a fact attached to node. Returns true if this is a new
// fact at this byte range; used by the scheduler to detect convergence
// in fixpoint groups.
func (s *Store) Emit(kind string, node tsutil.Node, payload map[string]any) bool {
	k := Key{FileID: node.FileID, StartByte: node.StartByte(), EndByte: node.EndByte(), Kind: kind}
	fact := Fact{
		Kind:      kind,
		FileID:    node.FileID,
		StartByte: node.StartByte(),
		EndByte:   node.EndByte(),
		Payload:   payload,
	}
	isIdent := identifierTypes[node.Type()]
	var nameKey NameKey
	if isIdent {
		nameKey = NameKey{Name: node.Text(), Kind: kind}
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	_, exists := s.byRange[k]
	s.byRange[k] = fact
	if isIdent {
		facts := s.byName[nameKey]
		replaced := false
		for i := range facts {
			if facts[i].site() == fact.site() {
				facts[i] = fact
				replaced = true
				break
			}
		}
		if !replaced {
			s.byName[nameKey] = append(facts, fact)
		}
	}
	return !exists
}

// Has reports whether a fact of the given kind is attached to node, or
// to the identifier with the same text that node binds to (see Get).
func (s *Store) Has(node tsutil.Node, kind string) bool {
	_, ok := s.Get(node, kind)
	return ok
}

// Get returns the fact of the given kind attached to node, or to the
// identifier with the same text that node binds to, or zero-value+false
// if there is none.
//
// When every fact of this kind on node's text is anchored on a
// definition, and node's language defines that text, node binds to the
// definition nearest to it in its language, and Get returns that
// definition's fact, if it has one. Otherwise node binds to the nearest
// fact with its text. Nearest means, in order: the
// same file, the same directory, the deepest common directory, and a
// file of the same kind, test or non-test.
func (s *Store) Get(node tsutil.Node, kind string) (Fact, bool) {
	if s == nil {
		return Fact{}, false
	}
	rk := Key{FileID: node.FileID, StartByte: node.StartByte(), EndByte: node.EndByte(), Kind: kind}
	s.mu.RLock()
	defer s.mu.RUnlock()
	if f, ok := s.byRange[rk]; ok {
		return f, true
	}
	if !identifierTypes[node.Type()] {
		return Fact{}, false
	}
	text := node.Text()
	facts := s.byName[NameKey{Name: text, Kind: kind}]
	if len(facts) == 0 {
		return Fact{}, false
	}
	defs := s.defs[defKeyOf(node)]
	allDefs := len(defs) > 0
	for _, f := range facts {
		if !s.isDef[f.site()] {
			allDefs = false
			break
		}
	}
	if allDefs {
		d := s.nearest(node.FileID, defs)
		f, ok := s.byRange[Key{FileID: d.FileID, StartByte: d.StartByte, EndByte: d.EndByte, Kind: kind}]
		return f, ok
	}
	sites := make([]site, len(facts))
	for i, f := range facts {
		sites[i] = f.site()
	}
	d := s.nearest(node.FileID, sites)
	for _, f := range facts {
		if f.site() == d {
			return f, true
		}
	}
	return Fact{}, false
}

// nearest returns the site in sites, which must be non-empty, nearest
// to a query in the file from.
func (s *Store) nearest(from string, sites []site) site {
	best := sites[0]
	for _, c := range sites[1:] {
		if s.compareNearness(from, c, best) < 0 {
			best = c
		}
	}
	return best
}

// compareNearness returns a negative number when a is nearer than b to
// a query in the file from, and a positive number when b is nearer. Ties
// fall to the file ID and offset, so the result doesn't depend on the
// order in which files were analyzed.
func (s *Store) compareNearness(from string, a, b site) int {
	fromDir := path.Dir(slash(from))
	aDir, bDir := path.Dir(slash(a.FileID)), path.Dir(slash(b.FileID))
	fromTest := s.test(from)
	return cmp.Or(
		boolFirst(a.FileID == from, b.FileID == from),
		boolFirst(aDir == fromDir, bDir == fromDir),
		cmp.Compare(commonDepth(bDir, fromDir), commonDepth(aDir, fromDir)),
		boolFirst(s.test(a.FileID) == fromTest, s.test(b.FileID) == fromTest),
		cmp.Compare(a.FileID, b.FileID),
		cmp.Compare(a.StartByte, b.StartByte),
	)
}

// boolFirst orders true before false.
func boolFirst(a, b bool) int {
	switch {
	case a == b:
		return 0
	case a:
		return -1
	default:
		return 1
	}
}

// commonDepth returns how many leading directory components a and b
// share.
func commonDepth(a, b string) int {
	as, bs := strings.Split(a, "/"), strings.Split(b, "/")
	n := 0
	for n < len(as) && n < len(bs) && as[n] == bs[n] {
		n++
	}
	return n
}

func slash(p string) string { return strings.ReplaceAll(p, `\`, "/") }

func (s *Store) test(fileID string) bool {
	if v, ok := s.isTest.Load(fileID); ok {
		return v.(bool)
	}
	t := testpath.Is(fileID)
	s.isTest.Store(fileID, t)
	return t
}

// Len returns the total number of facts (by-range only).
func (s *Store) Len() int {
	if s == nil {
		return 0
	}
	s.mu.RLock()
	defer s.mu.RUnlock()
	return len(s.byRange)
}

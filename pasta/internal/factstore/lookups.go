package factstore

import "github.com/imjasonh/playground/pasta/internal/tsutil"

// Lookups is a set of the store entries that Has consults: a fact's key,
// and, for an identifier, its text and kind. A fact emitted later can
// change the answer to a lookup only when it adds one of those entries.
type Lookups struct {
	ranges map[Key]bool
	names  map[NameKey]bool
}

// Empty reports whether l holds no entries.
func (l *Lookups) Empty() bool {
	return l == nil || len(l.ranges)+len(l.names) == 0
}

// Overlaps reports whether l and o share an entry.
func (l *Lookups) Overlaps(o *Lookups) bool {
	if l.Empty() || o.Empty() {
		return false
	}
	return overlap(l.ranges, o.ranges) || overlap(l.names, o.names)
}

func overlap[K comparable](a, b map[K]bool) bool {
	if len(a) > len(b) {
		a, b = b, a
	}
	for k := range a {
		if b[k] {
			return true
		}
	}
	return false
}

func (l *Lookups) addRange(k Key) {
	if l.ranges == nil {
		l.ranges = map[Key]bool{}
	}
	l.ranges[k] = true
}

func (l *Lookups) addName(k NameKey) {
	if l.names == nil {
		l.names = map[NameKey]bool{}
	}
	l.names[k] = true
}

// Recorder answers Has from Store and adds each lookup to Lookups.
type Recorder struct {
	Store   *Store
	Lookups *Lookups
}

// Has records the lookup and returns Store.Has(node, kind).
func (r Recorder) Has(node tsutil.Node, kind string) bool {
	r.Lookups.addRange(Key{FileID: node.FileID, StartByte: node.StartByte(), EndByte: node.EndByte(), Kind: kind})
	if identifierTypes[node.Type()] {
		r.Lookups.addName(NameKey{Name: node.Text(), Kind: kind})
	}
	return r.Store.Has(node, kind)
}

// Mark returns the number of entries facts have added to the store, to
// pass to Added later.
func (s *Store) Mark() int {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return len(s.added)
}

// Added returns the entries that facts emitted since mark added.
func (s *Store) Added(mark int) *Lookups {
	s.mu.RLock()
	defer s.mu.RUnlock()
	l := &Lookups{}
	for _, a := range s.added[mark:] {
		if a.newRange {
			l.addRange(a.key)
		}
		if a.named {
			l.addName(a.name)
		}
	}
	return l
}

// addition is one entry in the store's log of new entries.
type addition struct {
	key      Key
	name     NameKey
	newRange bool
	named    bool
}

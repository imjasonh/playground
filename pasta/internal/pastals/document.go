package pastals

import (
	"sync"

	"github.com/imjasonh/pasta/internal/pastals/lspconv"
)

// document is an in-memory snapshot of an open file.
//
// Mutations go through update under mu. Diagnostic goroutines never
// read the live fields; they receive a docSnapshot copied at schedule
// time so didChange cannot race with an in-flight analysis.
type document struct {
	mu      sync.Mutex
	uri     string
	path    string // local filesystem path derived from URI
	version int
	src     []byte
	conv    *lspconv.Doc
}

// docSnapshot is an immutable copy of a document at one version.
type docSnapshot struct {
	uri     string
	path    string
	version int
	src     []byte
	conv    *lspconv.Doc
}

// docStore is a concurrency-safe map of open documents.
type docStore struct {
	mu sync.RWMutex
	m  map[string]*document
}

func newDocStore() *docStore {
	return &docStore{m: map[string]*document{}}
}

func (s *docStore) put(d *document) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.m[d.uri] = d
}

func (s *docStore) get(uri string) (*document, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	d, ok := s.m[uri]
	return d, ok
}

func (s *docStore) delete(uri string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.m, uri)
}

func (s *docStore) all() []*document {
	s.mu.RLock()
	defer s.mu.RUnlock()
	out := make([]*document, 0, len(s.m))
	for _, d := range s.m {
		out = append(out, d)
	}
	return out
}

// update replaces the document's text and rebuilds its lspconv.Doc.
func (d *document) update(version int, text string) {
	d.mu.Lock()
	defer d.mu.Unlock()
	d.version = version
	d.src = []byte(text)
	d.conv = lspconv.New(d.src)
}

// snapshot returns an immutable copy suitable for concurrent analysis.
func (d *document) snapshot() docSnapshot {
	d.mu.Lock()
	defer d.mu.Unlock()
	src := make([]byte, len(d.src))
	copy(src, d.src)
	return docSnapshot{
		uri:     d.uri,
		path:    d.path,
		version: d.version,
		src:     src,
		// Rebuild conv from the copied bytes so the snapshot does not
		// share mutable state with later updates.
		conv: lspconv.New(src),
	}
}

// currentVersion returns the document's latest version under lock.
func (d *document) currentVersion() int {
	d.mu.Lock()
	defer d.mu.Unlock()
	return d.version
}

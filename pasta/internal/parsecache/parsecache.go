// Package parsecache stores per-file rule results across pasta runs.
//
// The cache is content-addressed: a file's key is the SHA-256 of its
// source bytes combined with its language name, and the entire rule
// set is hashed once per run, with the embedded grammar build, to scope
// entries by the rules and parser that produced them. A cache HIT lets pasta skip parsing AND rule
// matching for files that haven't changed since the last run — the
// stored diagnostics and edit ops are returned directly.
//
// Correctness depends on the engine's streaming mode: cached results
// are only valid when each file's output depends solely on its own
// bytes. The engine consults canStream before consulting the cache;
// rules with cross-file `requires` or fixpoint groups bypass it.
//
// Those runs use the tree half of the cache instead: a file's compact
// parse tree, which depends only on its bytes, its language, and the
// grammar build, so it survives rule changes.
//
// Storage layout:
//
//	<dir>/<schema_version>/<rule_hash>/<file_hash>.gob
//	<dir>/<schema_version>/trees-<build_id>/<file_hash>.tree
//
// Schema version is bumped when the on-disk Entry format changes.
// The rule_hash subdirectory keeps different rule sets from
// colliding so a project can iterate on rules without poisoning a
// neighbour's cache.
//
// LRU eviction is mtime-driven: reads `touch` the file so recently
// used entries survive the next prune, and Prune deletes oldest-
// first until total size is under the configured limit.
package parsecache

import (
	"crypto/sha256"
	"encoding/gob"
	"encoding/hex"
	"encoding/json/v2"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/pasta/internal/dsl"
	"github.com/imjasonh/playground/pasta/internal/effect"
	"github.com/imjasonh/playground/pasta/internal/treesitter"
)

// schemaVersion segregates entries written by different pasta
// versions. Bump when the on-disk Entry struct changes shape or when
// engine semantics shift in a way that invalidates prior runs.
// v2: engine skips ERROR-heavy trees and no longer caches them; prior
// v1 entries may still hold diagnostics/ops for those files.
// v3: entries record parse-error skips and degraded trees.
const schemaVersion = "v3"

// Entry is the cached output for one (rule-set, file) pair.
type Entry struct {
	Diagnostics []effect.Diagnostic
	Ops         []effect.Op
	// SkipReason is the engine's reason for not analyzing the file, or
	// empty when it was analyzed.
	SkipReason string
	// Degraded is true when the tree had parse errors but was analyzed.
	Degraded bool
}

// Cache reads and writes per-file results from a directory on disk.
// A nil *Cache is a valid no-op: Get always misses and Put discards.
// Pass nil through call sites to disable caching transparently.
type Cache struct {
	dir       string
	ruleHash  string
	sizeLimit int64

	hits   atomic.Int64
	misses atomic.Int64
	writes atomic.Int64

	treeHits   atomic.Int64
	treeMisses atomic.Int64
	treeWrites atomic.Int64
}

// Stats reports how the cache performed during a run. Returned by
// the engine for the CLI to print or log.
type Stats struct {
	Hits, Misses, Writes             int64
	TreeHits, TreeMisses, TreeWrites int64
}

// Open prepares dir/<schemaVersion>/<ruleHash>/ for use. sizeLimit
// bounds total cache size in bytes across all rule subdirectories; 0
// means unbounded. Returns a valid *Cache even if MkdirAll fails —
// the cache simply degrades to no-op so a transient disk error
// doesn't break the run.
func Open(dir string, ruleHash string, sizeLimit int64) *Cache {
	if dir == "" || ruleHash == "" {
		return nil
	}
	c := &Cache{dir: dir, ruleHash: ruleHash, sizeLimit: sizeLimit}
	for _, d := range []string{filepath.Join(dir, schemaVersion, ruleHash), c.treeDir()} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			return nil
		}
	}
	return c
}

// Dir returns the root cache directory.
func (c *Cache) Dir() string {
	if c == nil {
		return ""
	}
	return c.dir
}

// Stats returns a snapshot of hit / miss / write counters.
func (c *Cache) Stats() Stats {
	if c == nil {
		return Stats{}
	}
	return Stats{
		Hits:       c.hits.Load(),
		Misses:     c.misses.Load(),
		Writes:     c.writes.Load(),
		TreeHits:   c.treeHits.Load(),
		TreeMisses: c.treeMisses.Load(),
		TreeWrites: c.treeWrites.Load(),
	}
}

// HashFile returns a stable key for (lang, src). Combines both so two
// files with identical bytes but different languages don't collide.
func HashFile(lang string, src []byte) string {
	h := sha256.New()
	h.Write([]byte(lang))
	h.Write([]byte{0})
	h.Write(src)
	return hex.EncodeToString(h.Sum(nil))
}

// HashRules returns a stable hash of the loaded analyzer set and the
// embedded grammar build. Analyzers are sorted by name before encoding
// so iteration order in the caller doesn't matter. Predicate functions and other non-serializable
// fields are out of scope here — the rule's JSON shape is the
// canonical input to the matcher, so it's a sufficient identity for
// cache correctness.
func HashRules(analyzers []*dsl.Analyzer) string {
	type named struct {
		Name string
		A    *dsl.Analyzer
	}
	ns := make([]named, len(analyzers))
	for i, a := range analyzers {
		ns[i] = named{Name: a.Name, A: a}
	}
	sort.Slice(ns, func(i, j int) bool { return ns[i].Name < ns[j].Name })

	h := sha256.New()
	h.Write([]byte(schemaVersion))
	h.Write([]byte(treesitter.BuildID()))
	for _, n := range ns {
		if err := json.MarshalWrite(h, n.A, json.Deterministic(true)); err != nil {
			return ""
		}
		h.Write([]byte("\n"))
	}
	return hex.EncodeToString(h.Sum(nil))
}

// entryPath returns the on-disk path for a given file hash.
func (c *Cache) entryPath(fileHash string) string {
	return filepath.Join(c.dir, schemaVersion, c.ruleHash, fileHash+".gob")
}

// Get reads the cached entry for fileHash. Returns (zero, false) on
// miss or any decode/IO error — callers re-run the analysis on miss,
// so a corrupt entry is self-healing.
//
// On hit, touches the file's mtime so the next Prune treats it as
// recently used.
func (c *Cache) Get(fileHash string) (Entry, bool) {
	if c == nil {
		return Entry{}, false
	}
	path := c.entryPath(fileHash)
	f, err := os.Open(path)
	if err != nil {
		c.misses.Add(1)
		return Entry{}, false
	}
	defer f.Close()
	var e Entry
	if err := gob.NewDecoder(f).Decode(&e); err != nil {
		c.misses.Add(1)
		return Entry{}, false
	}
	now := time.Now()
	_ = os.Chtimes(path, now, now)
	c.hits.Add(1)
	return e, true
}

// Put writes entry under fileHash. Failures (full disk, racing
// writer, permission denied) are swallowed: caching is best-effort
// and the engine has already computed the entry it'd be storing.
func (c *Cache) Put(fileHash string, e Entry) {
	if c == nil {
		return
	}
	if writeFile(c.entryPath(fileHash), func(w io.Writer) error { return gob.NewEncoder(w).Encode(e) }) {
		c.writes.Add(1)
	}
}

// treeDir returns the directory of the trees of this grammar build.
func (c *Cache) treeDir() string {
	return filepath.Join(c.dir, schemaVersion, "trees-"+treesitter.BuildID())
}

// GetTree reads the compact parse tree stored under fileHash. Returns
// (nil, false) on miss or IO error. The caller decodes the tree and
// parses the file when that fails, so a corrupt entry costs one parse.
// On hit, touches the file's mtime so the next Prune keeps it.
func (c *Cache) GetTree(fileHash string) (treesitter.Compact, bool) {
	if c == nil {
		return nil, false
	}
	path := filepath.Join(c.treeDir(), fileHash+".tree")
	b, err := os.ReadFile(path)
	if err != nil {
		c.treeMisses.Add(1)
		return nil, false
	}
	now := time.Now()
	_ = os.Chtimes(path, now, now)
	c.treeHits.Add(1)
	return b, true
}

// PutTree stores t under fileHash. Failures are swallowed, like Put's.
func (c *Cache) PutTree(fileHash string, t treesitter.Compact) {
	if c == nil {
		return
	}
	path := filepath.Join(c.treeDir(), fileHash+".tree")
	if writeFile(path, func(w io.Writer) error { _, err := w.Write(t); return err }) {
		c.treeWrites.Add(1)
	}
}

// writeFile writes path through a temporary file in its directory and
// renames it into place, so readers never see a partial file. It
// reports whether the file was written.
func writeFile(path string, write func(io.Writer) error) bool {
	tmp, err := os.CreateTemp(filepath.Dir(path), ".tmp-*")
	if err != nil {
		return false
	}
	if err := write(tmp); err != nil {
		tmp.Close()
		os.Remove(tmp.Name())
		return false
	}
	if err := tmp.Close(); err != nil {
		os.Remove(tmp.Name())
		return false
	}
	if err := os.Rename(tmp.Name(), path); err != nil {
		os.Remove(tmp.Name())
		return false
	}
	return true
}

// Prune walks the cache root and deletes oldest-mtime entries until
// total size is at or below sizeLimit. No-op when sizeLimit is 0.
// Walks ALL rule subdirectories — entries from a previous rule set
// are candidates for eviction the same as the current set.
func (c *Cache) Prune() error {
	if c == nil || c.sizeLimit == 0 {
		return nil
	}
	root := filepath.Join(c.dir, schemaVersion)
	var files []entryInfo
	var total int64
	if err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			// Don't abort the prune over a single bad subdir.
			return nil
		}
		if d.IsDir() {
			return nil
		}
		info, err := d.Info()
		if err != nil {
			return nil
		}
		files = append(files, entryInfo{path: p, size: info.Size(), mtime: info.ModTime()})
		total += info.Size()
		return nil
	}); err != nil || total <= c.sizeLimit {
		return err
	}
	sort.Slice(files, func(i, j int) bool { return files[i].mtime.Before(files[j].mtime) })
	for _, f := range files {
		if total <= c.sizeLimit {
			break
		}
		if err := os.Remove(f.path); err == nil {
			total -= f.size
		}
	}
	return nil
}

type entryInfo struct {
	path  string
	size  int64
	mtime time.Time
}

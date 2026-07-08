// Package store is a filesystem-backed AST object store used as the "remote"
// side of git-remote-ast.
//
// Layout:
//
//	<root>/
//	  refs/heads/<name>          → tip commit OID (40 hex)
//	  refs/tags/<name>
//	  HEAD                       → "ref: refs/heads/main"
//	  objects/<oid[0:2]>/<oid[2:]>.meta.json
//	  objects/<oid[0:2]>/<oid[2:]>.bin   → encoded payload (gzip)
//
// Objects are keyed by the *original git blob/tree/commit OID* so the helper
// can answer fetch/push without rewriting history. Blob payloads may be
// AST-compressed; trees and commits are stored as gzip(raw) for simplicity
// (they are already compact).
package store

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// Object kinds mirror git.
const (
	KindBlob   = "blob"
	KindTree   = "tree"
	KindCommit = "commit"
	KindTag    = "tag"
)

// Meta describes one stored object.
type Meta struct {
	OID       string `json:"oid"`
	Kind      string `json:"kind"`
	Encoding  string `json:"encoding"` // codec.Encoding*
	Size      int    `json:"size"`     // original uncompressed size
	Payload   int    `json:"payload"`  // stored payload size
	Lang      string `json:"lang,omitempty"`
	PathHint  string `json:"path_hint,omitempty"`
}

// Store is a directory-backed remote.
type Store struct {
	Root string
}

// Open creates or opens a store at root.
func Open(root string) (*Store, error) {
	s := &Store{Root: root}
	for _, d := range []string{
		filepath.Join(root, "objects"),
		filepath.Join(root, "refs", "heads"),
		filepath.Join(root, "refs", "tags"),
	} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			return nil, err
		}
	}
	head := filepath.Join(root, "HEAD")
	if _, err := os.Stat(head); errors.Is(err, os.ErrNotExist) {
		if err := os.WriteFile(head, []byte("ref: refs/heads/main\n"), 0o644); err != nil {
			return nil, err
		}
	}
	return s, nil
}

func (s *Store) objectPaths(oid string) (meta, bin string, err error) {
	oid = strings.ToLower(strings.TrimSpace(oid))
	if len(oid) != 40 {
		return "", "", fmt.Errorf("invalid oid %q", oid)
	}
	dir := filepath.Join(s.Root, "objects", oid[:2])
	return filepath.Join(dir, oid[2:]+".meta.json"), filepath.Join(dir, oid[2:]+".bin"), nil
}

// Has reports whether oid is present.
func (s *Store) Has(oid string) bool {
	meta, _, err := s.objectPaths(oid)
	if err != nil {
		return false
	}
	_, err = os.Stat(meta)
	return err == nil
}

// Put writes an object. Existing objects are left unchanged (content-addressed).
func (s *Store) Put(m Meta, payload []byte) error {
	metaPath, binPath, err := s.objectPaths(m.OID)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(metaPath), 0o755); err != nil {
		return err
	}
	if _, err := os.Stat(metaPath); err == nil {
		return nil
	}
	m.Payload = len(payload)
	b, err := json.MarshalIndent(m, "", "  ")
	if err != nil {
		return err
	}
	tmpBin := binPath + ".tmp"
	tmpMeta := metaPath + ".tmp"
	if err := os.WriteFile(tmpBin, payload, 0o644); err != nil {
		return err
	}
	if err := os.WriteFile(tmpMeta, append(b, '\n'), 0o644); err != nil {
		_ = os.Remove(tmpBin)
		return err
	}
	if err := os.Rename(tmpBin, binPath); err != nil {
		return err
	}
	return os.Rename(tmpMeta, metaPath)
}

// Get returns metadata and payload for oid.
func (s *Store) Get(oid string) (Meta, []byte, error) {
	metaPath, binPath, err := s.objectPaths(oid)
	if err != nil {
		return Meta{}, nil, err
	}
	mb, err := os.ReadFile(metaPath)
	if err != nil {
		return Meta{}, nil, err
	}
	var m Meta
	if err := json.Unmarshal(mb, &m); err != nil {
		return Meta{}, nil, err
	}
	payload, err := os.ReadFile(binPath)
	if err != nil {
		return Meta{}, nil, err
	}
	return m, payload, nil
}

// ListRefs returns refname → oid for all refs under refs/.
func (s *Store) ListRefs() (map[string]string, error) {
	out := map[string]string{}
	refsRoot := filepath.Join(s.Root, "refs")
	err := filepath.WalkDir(refsRoot, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		rel, err := filepath.Rel(s.Root, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		b, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		oid := strings.TrimSpace(string(b))
		if len(oid) == 40 {
			out[rel] = oid
		}
		return nil
	})
	return out, err
}

// ReadHEAD returns the symbolic or peeled HEAD.
func (s *Store) ReadHEAD() (string, error) {
	b, err := os.ReadFile(filepath.Join(s.Root, "HEAD"))
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(string(b)), nil
}

// UpdateRef writes refs/<...> to oid (or deletes if oid == "").
func (s *Store) UpdateRef(name, oid string) error {
	name = strings.TrimPrefix(name, "/")
	if !strings.HasPrefix(name, "refs/") {
		return fmt.Errorf("ref must start with refs/: %s", name)
	}
	path := filepath.Join(s.Root, filepath.FromSlash(name))
	if oid == "" {
		return os.Remove(path)
	}
	if len(oid) != 40 {
		return fmt.Errorf("invalid oid %q", oid)
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	tmp := path + ".tmp"
	if err := os.WriteFile(tmp, []byte(oid+"\n"), 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}

// Stats summarizes stored object sizes.
type Stats struct {
	Objects       int
	RawBytes      int64
	PayloadBytes  int64
	ASTObjects    int
	RawObjects    int
}

// ComputeStats walks all objects.
func (s *Store) ComputeStats() (Stats, error) {
	var st Stats
	err := filepath.WalkDir(filepath.Join(s.Root, "objects"), func(path string, d os.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, ".meta.json") {
			return err
		}
		b, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		var m Meta
		if err := json.Unmarshal(b, &m); err != nil {
			return err
		}
		st.Objects++
		st.RawBytes += int64(m.Size)
		st.PayloadBytes += int64(m.Payload)
		switch m.Encoding {
		case "ast-gzip", "ast-dict":
			st.ASTObjects++
		default:
			st.RawObjects++
		}
		return nil
	})
	return st, err
}

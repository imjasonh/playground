package tables

import (
	"fmt"
	"path"
	"strings"

	"github.com/go-git/go-git/v5/plumbing/filemode"
	"github.com/go-git/go-git/v5/plumbing/object"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

const filesSchema = `CREATE TABLE files(
	path      TEXT,
	name      TEXT,
	mode      TEXT,
	type      TEXT,
	size      INTEGER,
	blob_hash TEXT,
	is_binary INTEGER,
	lines     INTEGER,
	ref       TEXT HIDDEN
)`

const (
	fPath = iota
	fName
	fMode
	fType
	fSize
	fBlobHash
	fIsBinary
	fLines
	fRef
)

func init() {
	add(def{
		module:   "git_files",
		friendly: "files",
		schema:   filesSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &filesSource{repo: repo}, filesSchema, nil
		},
	})
}

type filesSource struct{ repo *gitrepo.Repo }

func (s *filesSource) BestIndex(info *fdw.IndexInfo) error {
	eqFilter(info, map[int]bool{fRef: true}, map[int]bool{fRef: true}, nil)
	return nil
}

func (s *filesSource) Open() (fdw.Cursor, error) { return &filesCursor{repo: s.repo}, nil }
func (s *filesSource) Disconnect() error         { return nil }
func (s *filesSource) Destroy() error            { return nil }

type filesEntry struct {
	path string
	mode filemode.FileMode
	hash string
	gh   object.TreeEntry
}

type filesCursor struct {
	repo  *gitrepo.Repo
	ref   string
	walk  *object.TreeWalker
	cur   *filesEntry
	rowid int64

	// lazy per-row blob content cache
	loaded  bool
	content []byte
	readErr error
}

func (c *filesCursor) Filter(_ int, idxStr string, args []fdw.Value) error {
	c.close()
	c.rowid = 0
	f := parseFilters(idxStr, args)
	ref, _ := filterText(f, fRef)

	commit, label, err := startCommit(c.repo, ref)
	if err != nil {
		return err
	}
	c.ref = label
	tree, err := commit.Tree()
	if err != nil {
		return err
	}
	c.walk = object.NewTreeWalker(tree, true, nil)
	return c.advance()
}

func (c *filesCursor) advance() error {
	for {
		name, entry, err := c.walk.Next()
		if err != nil {
			c.cur = nil // io.EOF or error ends the scan
			return nil
		}
		if entry.Mode == filemode.Dir {
			continue
		}
		c.cur = &filesEntry{path: name, mode: entry.Mode, hash: entry.Hash.String(), gh: entry}
		c.rowid++
		c.loaded, c.content, c.readErr = false, nil, nil
		return nil
	}
}

func (c *filesCursor) Next() error { return c.advance() }
func (c *filesCursor) EOF() bool   { return c.cur == nil }

// load reads (and caches) the current blob's bytes for size/binary/line columns.
func (c *filesCursor) load() ([]byte, error) {
	if c.loaded {
		return c.content, c.readErr
	}
	c.loaded = true
	if c.cur.mode == filemode.Submodule {
		return nil, nil
	}
	c.content, c.readErr = blobBytes(c.repo, c.cur.gh.Hash, 0)
	return c.content, c.readErr
}

func (c *filesCursor) Column(n int) (fdw.Value, error) {
	e := c.cur
	if e == nil {
		return fdw.NullValue(), nil
	}
	switch n {
	case fPath:
		return text(e.path), nil
	case fName:
		return text(path.Base(e.path)), nil
	case fMode:
		return text(fmt.Sprintf("%06o", uint32(e.mode))), nil
	case fType:
		return text(fileType(e.mode)), nil
	case fSize:
		if e.mode == filemode.Submodule {
			return fdw.NullValue(), nil
		}
		b, err := c.load()
		if err != nil {
			return fdw.NullValue(), err
		}
		return intval(int64(len(b))), nil
	case fBlobHash:
		return text(e.hash), nil
	case fIsBinary:
		if e.mode == filemode.Submodule {
			return fdw.NullValue(), nil
		}
		b, err := c.load()
		if err != nil {
			return fdw.NullValue(), err
		}
		return boolval(looksBinary(b)), nil
	case fLines:
		if e.mode == filemode.Submodule {
			return fdw.NullValue(), nil
		}
		b, err := c.load()
		if err != nil {
			return fdw.NullValue(), err
		}
		if looksBinary(b) {
			return fdw.NullValue(), nil
		}
		return intval(int64(countLines(b))), nil
	case fRef:
		return textOrNull(c.ref), nil
	}
	return fdw.NullValue(), nil
}

func (c *filesCursor) RowID() (int64, error) { return c.rowid, nil }

func (c *filesCursor) Close() error { c.close(); return nil }

func (c *filesCursor) close() {
	if c.walk != nil {
		c.walk.Close()
		c.walk = nil
	}
	c.cur = nil
}

func fileType(m filemode.FileMode) string {
	switch m {
	case filemode.Executable:
		return "executable"
	case filemode.Symlink:
		return "symlink"
	case filemode.Submodule:
		return "submodule"
	default:
		return "file"
	}
}

func countLines(b []byte) int {
	if len(b) == 0 {
		return 0
	}
	n := strings.Count(string(b), "\n")
	if b[len(b)-1] != '\n' {
		n++
	}
	return n
}

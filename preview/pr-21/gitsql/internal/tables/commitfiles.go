package tables

import (
	"io"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

const commitFilesSchema = `CREATE TABLE commit_files(
	commit_hash TEXT,
	path        TEXT,
	old_path    TEXT,
	change      TEXT,
	additions   INTEGER,
	deletions   INTEGER,
	binary      INTEGER,
	ref         TEXT HIDDEN
)`

const (
	cfCommitHash = iota
	cfPath
	cfOldPath
	cfChange
	cfAdditions
	cfDeletions
	cfBinary
	cfRef
)

func init() {
	add(def{
		module:   "git_commit_files",
		friendly: "commit_files",
		schema:   commitFilesSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &commitFilesSource{repo: repo}, commitFilesSchema, nil
		},
	})
}

type commitFilesSource struct{ repo *gitrepo.Repo }

func (s *commitFilesSource) BestIndex(info *fdw.IndexInfo) error {
	eqFilter(info,
		map[int]bool{cfCommitHash: true, cfRef: true},
		map[int]bool{cfCommitHash: true, cfRef: true},
		nil,
	)
	return nil
}

func (s *commitFilesSource) Open() (fdw.Cursor, error) {
	return &commitFilesCursor{repo: s.repo}, nil
}
func (s *commitFilesSource) Disconnect() error { return nil }
func (s *commitFilesSource) Destroy() error    { return nil }

type commitFilesCursor struct {
	repo *gitrepo.Repo
	ref  string

	iter    object.CommitIter // nil in single-commit mode
	single  bool
	hash    plumbing.Hash
	pending []gitrepo.FileChange
	idx     int
	rowid   int64
	err     error
}

func (c *commitFilesCursor) Filter(_ int, idxStr string, args []fdw.Value) error {
	c.reset()
	f := parseFilters(idxStr, args)

	if h, ok := filterText(f, cfCommitHash); ok {
		c.single = true
		commit, err := c.repo.Git().CommitObject(plumbing.NewHash(h))
		if err != nil {
			return nil // unknown commit → empty
		}
		c.hash = commit.Hash
		changes, err := c.repo.CommitChanges(commit)
		if err != nil {
			return err
		}
		c.pending = changes
		return c.skipEmpty()
	}

	ref, _ := filterText(f, cfRef)
	start, label, err := startCommit(c.repo, ref)
	if err != nil {
		return err
	}
	c.ref = label
	iter, err := c.repo.Git().Log(&git.LogOptions{From: start.Hash, Order: git.LogOrderCommitterTime})
	if err != nil {
		return err
	}
	c.iter = iter
	return c.loadNextCommit()
}

func (c *commitFilesCursor) reset() {
	if c.iter != nil {
		c.iter.Close()
	}
	*c = commitFilesCursor{repo: c.repo}
}

// loadNextCommit advances to the next commit that touched at least one file.
// Merge commits are skipped in a full scan: diffing a merge against its first
// parent re-attributes every change from the merged branch (double-counting for
// churn/authorship) and is the most expensive diff in the repo. This matches
// `git log --numstat`, which shows nothing for merges by default. An explicit
// `WHERE commit_hash = '<merge>'` still returns the first-parent diff.
func (c *commitFilesCursor) loadNextCommit() error {
	for {
		commit, err := c.iter.Next()
		if err == io.EOF {
			c.pending, c.hash = nil, plumbing.ZeroHash
			return nil
		}
		if err != nil {
			c.err = err
			c.pending = nil
			return err
		}
		if commit.NumParents() > 1 {
			continue
		}
		changes, err := c.repo.CommitChanges(commit)
		if err != nil {
			return err
		}
		if len(changes) == 0 {
			continue
		}
		c.hash, c.pending, c.idx = commit.Hash, changes, 0
		c.rowid++
		return nil
	}
}

// skipEmpty is used in single-commit mode to present the (possibly empty) slice.
func (c *commitFilesCursor) skipEmpty() error {
	if len(c.pending) == 0 {
		c.hash = plumbing.ZeroHash
		return nil
	}
	c.idx, c.rowid = 0, 1
	return nil
}

func (c *commitFilesCursor) Next() error {
	c.idx++
	if c.idx < len(c.pending) {
		c.rowid++
		return nil
	}
	if c.single {
		c.pending = nil
		return nil
	}
	return c.loadNextCommit()
}

func (c *commitFilesCursor) EOF() bool { return c.idx >= len(c.pending) }

func (c *commitFilesCursor) Column(n int) (fdw.Value, error) {
	if c.idx >= len(c.pending) {
		return fdw.NullValue(), nil
	}
	fc := c.pending[c.idx]
	switch n {
	case cfCommitHash:
		return text(c.hash.String()), nil
	case cfPath:
		return text(fc.Path), nil
	case cfOldPath:
		return text(fc.OldPath), nil
	case cfChange:
		return text(fc.Change), nil
	case cfAdditions:
		return intval(int64(fc.Additions)), nil
	case cfDeletions:
		return intval(int64(fc.Deletions)), nil
	case cfBinary:
		return boolval(fc.Binary), nil
	case cfRef:
		return textOrNull(c.ref), nil
	}
	return fdw.NullValue(), nil
}

func (c *commitFilesCursor) RowID() (int64, error) { return c.rowid, nil }

func (c *commitFilesCursor) Close() error {
	if c.iter != nil {
		c.iter.Close()
		c.iter = nil
	}
	return nil
}

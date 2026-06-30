package tables

import (
	"io"
	"strings"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

const commitsSchema = `CREATE TABLE commits(
	hash            TEXT,
	author_name     TEXT,
	author_email    TEXT,
	author_when     TEXT,
	author_unix     INTEGER,
	committer_name  TEXT,
	committer_email TEXT,
	committer_when  TEXT,
	committer_unix  INTEGER,
	message         TEXT,
	summary         TEXT,
	parents         INTEGER,
	parent_hashes   TEXT,
	tree_hash       TEXT,
	is_merge        INTEGER,
	ref             TEXT HIDDEN
)`

// commits column indices.
const (
	cCommitHash = iota
	cAuthorName
	cAuthorEmail
	cAuthorWhen
	cAuthorUnix
	cCommitterName
	cCommitterEmail
	cCommitterWhen
	cCommitterUnix
	cMessage
	cSummary
	cParents
	cParentHashes
	cTreeHash
	cIsMerge
	cRef
)

func init() {
	add(def{
		module:   "git_commits",
		friendly: "commits",
		schema:   commitsSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &commitsSource{repo: repo}, commitsSchema, nil
		},
	})
}

type commitsSource struct{ repo *gitrepo.Repo }

func (s *commitsSource) BestIndex(info *fdw.IndexInfo) error {
	eqFilter(info,
		map[int]bool{cCommitHash: true, cRef: true},
		map[int]bool{cCommitHash: true, cRef: true},
		map[int]bool{cCommitHash: true},
	)
	return nil
}

func (s *commitsSource) Open() (fdw.Cursor, error) { return &commitsCursor{repo: s.repo}, nil }
func (s *commitsSource) Disconnect() error         { return nil }
func (s *commitsSource) Destroy() error            { return nil }

type commitsCursor struct {
	repo   *gitrepo.Repo
	iter   object.CommitIter
	cur    *object.Commit
	ref    string
	single bool
	rowid  int64
	err    error
}

func (c *commitsCursor) Filter(_ int, idxStr string, args []fdw.Value) error {
	c.reset()
	f := parseFilters(idxStr, args)

	if hash, ok := filterText(f, cCommitHash); ok {
		c.single = true
		commit, err := c.repo.Git().CommitObject(plumbing.NewHash(hash))
		if err != nil {
			// Unknown hash: empty result rather than a hard error.
			c.cur = nil
			return nil
		}
		c.cur = commit
		c.rowid = 1
		return nil
	}

	ref, _ := filterText(f, cRef)
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
	return c.advance()
}

func (c *commitsCursor) reset() {
	if c.iter != nil {
		c.iter.Close()
	}
	c.iter, c.cur, c.single, c.rowid, c.err = nil, nil, false, 0, nil
	c.ref = ""
}

func (c *commitsCursor) advance() error {
	commit, err := c.iter.Next()
	if err == io.EOF {
		c.cur = nil
		return nil
	}
	if err != nil {
		c.err = err
		c.cur = nil
		return err
	}
	c.cur = commit
	c.rowid++
	return nil
}

func (c *commitsCursor) Next() error {
	if c.single {
		c.cur = nil
		return nil
	}
	return c.advance()
}

func (c *commitsCursor) EOF() bool { return c.cur == nil }

func (c *commitsCursor) Column(n int) (fdw.Value, error) {
	cm := c.cur
	if cm == nil {
		return fdw.NullValue(), nil
	}
	switch n {
	case cCommitHash:
		return text(cm.Hash.String()), nil
	case cAuthorName:
		return text(cm.Author.Name), nil
	case cAuthorEmail:
		return text(cm.Author.Email), nil
	case cAuthorWhen:
		return text(wallClock(cm.Author.When)), nil
	case cAuthorUnix:
		return intval(cm.Author.When.Unix()), nil
	case cCommitterName:
		return text(cm.Committer.Name), nil
	case cCommitterEmail:
		return text(cm.Committer.Email), nil
	case cCommitterWhen:
		return text(wallClock(cm.Committer.When)), nil
	case cCommitterUnix:
		return intval(cm.Committer.When.Unix()), nil
	case cMessage:
		return text(strings.TrimRight(cm.Message, "\n")), nil
	case cSummary:
		return text(firstLine(cm.Message)), nil
	case cParents:
		return intval(int64(cm.NumParents())), nil
	case cParentHashes:
		hs := make([]string, len(cm.ParentHashes))
		for i, h := range cm.ParentHashes {
			hs[i] = h.String()
		}
		return text(strings.Join(hs, " ")), nil
	case cTreeHash:
		return text(cm.TreeHash.String()), nil
	case cIsMerge:
		return boolval(cm.NumParents() > 1), nil
	case cRef:
		return textOrNull(c.ref), nil
	}
	return fdw.NullValue(), nil
}

func (c *commitsCursor) RowID() (int64, error) { return c.rowid, nil }

func (c *commitsCursor) Close() error {
	if c.iter != nil {
		c.iter.Close()
	}
	return nil
}

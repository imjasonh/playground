package tables

import (
	"errors"

	"github.com/go-git/go-git/v5"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

const blameSchema = `CREATE TABLE blame(
	path         TEXT,
	line_no      INTEGER,
	content      TEXT,
	commit_hash  TEXT,
	author_name  TEXT,
	author_email TEXT,
	author_when  TEXT,
	author_unix  INTEGER,
	ref          TEXT HIDDEN
)`

const (
	bPath = iota
	bLineNo
	bContent
	bCommitHash
	bAuthorName
	bAuthorEmail
	bAuthorWhen
	bAuthorUnix
	bRef
)

func init() {
	add(def{
		module:   "git_blame",
		friendly: "blame",
		schema:   blameSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &blameSource{repo: repo}, blameSchema, nil
		},
	})
}

type blameSource struct{ repo *gitrepo.Repo }

func (s *blameSource) BestIndex(info *fdw.IndexInfo) error {
	eqFilter(info,
		map[int]bool{bPath: true, bRef: true},
		map[int]bool{bPath: true, bRef: true},
		nil,
	)
	// Blame is expensive; nudge the planner to push the path constraint.
	info.EstimatedCost = 1e6
	info.EstimatedRows = 1000
	return nil
}

func (s *blameSource) Open() (fdw.Cursor, error) { return &blameCursor{repo: s.repo}, nil }
func (s *blameSource) Disconnect() error         { return nil }
func (s *blameSource) Destroy() error            { return nil }

type blameCursor struct {
	repo   *gitrepo.Repo
	ref    string
	result *git.BlameResult
	pos    int
}

func (c *blameCursor) Filter(_ int, idxStr string, args []fdw.Value) error {
	c.result, c.pos = nil, 0
	f := parseFilters(idxStr, args)

	path, ok := filterText(f, bPath)
	if !ok || path == "" {
		return errors.New("blame requires a path: SELECT * FROM blame WHERE path = '<file>'")
	}
	ref, _ := filterText(f, bRef)
	commit, label, err := startCommit(c.repo, ref)
	if err != nil {
		return err
	}
	c.ref = label
	res, err := git.Blame(commit, path)
	if err != nil {
		return err
	}
	c.result = res
	return nil
}

func (c *blameCursor) Next() error { c.pos++; return nil }

func (c *blameCursor) EOF() bool {
	return c.result == nil || c.pos >= len(c.result.Lines)
}

func (c *blameCursor) Column(n int) (fdw.Value, error) {
	line := c.result.Lines[c.pos]
	switch n {
	case bPath:
		return text(c.result.Path), nil
	case bLineNo:
		return intval(int64(c.pos + 1)), nil
	case bContent:
		return text(line.Text), nil
	case bCommitHash:
		return text(line.Hash.String()), nil
	case bAuthorName:
		return text(line.AuthorName), nil
	case bAuthorEmail:
		return text(line.Author), nil
	case bAuthorWhen:
		return text(wallClock(line.Date)), nil
	case bAuthorUnix:
		return intval(line.Date.Unix()), nil
	case bRef:
		return textOrNull(c.ref), nil
	}
	return fdw.NullValue(), nil
}

func (c *blameCursor) RowID() (int64, error) { return int64(c.pos + 1), nil }
func (c *blameCursor) Close() error          { return nil }

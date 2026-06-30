package tables

import (
	"github.com/go-git/go-git/v5/plumbing"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
)

const refsSchema = `CREATE TABLE refs(
	name       TEXT,
	short_name TEXT,
	type       TEXT,
	target     TEXT,
	hash       TEXT,
	is_branch  INTEGER,
	is_tag     INTEGER,
	is_remote  INTEGER,
	is_head    INTEGER
)`

func init() {
	add(def{
		module:   "git_refs",
		friendly: "refs",
		schema:   refsSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &refsSource{repo: repo}, refsSchema, nil
		},
	})
}

type refRow struct {
	name, short, typ, target, hash    string
	isBranch, isTag, isRemote, isHead bool
}

type refsSource struct{ repo *gitrepo.Repo }

func (s *refsSource) BestIndex(info *fdw.IndexInfo) error {
	info.ConstraintUsage = make([]fdw.IndexConstraintUsage, len(info.Constraints))
	return nil
}

func (s *refsSource) Open() (fdw.Cursor, error) { return &refsCursor{repo: s.repo}, nil }
func (s *refsSource) Disconnect() error         { return nil }
func (s *refsSource) Destroy() error            { return nil }

type refsCursor struct {
	repo *gitrepo.Repo
	rows []refRow
	pos  int
}

func (c *refsCursor) Filter(_ int, _ string, _ []fdw.Value) error {
	c.rows, c.pos = nil, 0
	g := c.repo.Git()

	headName := ""
	if head, err := g.Head(); err == nil {
		headName = head.Name().String()
	}

	iter, err := g.References()
	if err != nil {
		return err
	}
	defer iter.Close()
	return iter.ForEach(func(ref *plumbing.Reference) error {
		name := ref.Name()
		row := refRow{
			name:     name.String(),
			short:    name.Short(),
			isBranch: name.IsBranch(),
			isTag:    name.IsTag(),
			isRemote: name.IsRemote(),
		}
		switch {
		case ref.Type() == plumbing.SymbolicReference:
			row.typ = "symbolic"
			row.target = ref.Target().String()
			if resolved, err := g.Reference(name, true); err == nil {
				row.hash = resolved.Hash().String()
			}
		default:
			row.target = ref.Hash().String()
			row.hash = ref.Hash().String()
		}
		switch {
		case row.isBranch:
			row.typ = "branch"
		case row.isTag:
			row.typ = "tag"
		case row.isRemote:
			row.typ = "remote"
		case row.typ == "":
			row.typ = "other"
		}
		row.isHead = name.String() == "HEAD" || (headName != "" && name.String() == headName)
		c.rows = append(c.rows, row)
		return nil
	})
}

func (c *refsCursor) Next() error { c.pos++; return nil }
func (c *refsCursor) EOF() bool   { return c.pos >= len(c.rows) }

func (c *refsCursor) Column(n int) (fdw.Value, error) {
	r := c.rows[c.pos]
	switch n {
	case 0:
		return text(r.name), nil
	case 1:
		return text(r.short), nil
	case 2:
		return text(r.typ), nil
	case 3:
		return text(r.target), nil
	case 4:
		return textOrNull(r.hash), nil
	case 5:
		return boolval(r.isBranch), nil
	case 6:
		return boolval(r.isTag), nil
	case 7:
		return boolval(r.isRemote), nil
	case 8:
		return boolval(r.isHead), nil
	}
	return fdw.NullValue(), nil
}

func (c *refsCursor) RowID() (int64, error) { return int64(c.pos + 1), nil }
func (c *refsCursor) Close() error          { return nil }

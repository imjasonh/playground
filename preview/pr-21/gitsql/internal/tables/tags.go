package tables

import (
	"strings"

	"github.com/go-git/go-git/v5/plumbing"
	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

const tagsSchema = `CREATE TABLE tags(
	name         TEXT,
	full_name    TEXT,
	type         TEXT,
	target       TEXT,
	tagger_name  TEXT,
	tagger_email TEXT,
	tagger_when  TEXT,
	tagger_unix  INTEGER,
	message      TEXT,
	tag_hash     TEXT
)`

func init() {
	add(def{
		module:   "git_tags",
		friendly: "tags",
		schema:   tagsSchema,
		factory: func(args fdw.ConnectArgs) (fdw.Source, string, error) {
			repo, err := resolveSpec(args)
			if err != nil {
				return nil, "", err
			}
			return &tagsSource{repo: repo}, tagsSchema, nil
		},
	})
}

type tagRow struct {
	name, full, typ, target          string
	taggerName, taggerEmail, message string
	taggerWhen                       string
	taggerUnix                       int64
	hasTagger                        bool
	tagHash                          string
}

type tagsSource struct{ repo *gitrepo.Repo }

func (s *tagsSource) BestIndex(info *fdw.IndexInfo) error {
	info.ConstraintUsage = make([]fdw.IndexConstraintUsage, len(info.Constraints))
	return nil
}

func (s *tagsSource) Open() (fdw.Cursor, error) { return &tagsCursor{repo: s.repo}, nil }
func (s *tagsSource) Disconnect() error         { return nil }
func (s *tagsSource) Destroy() error            { return nil }

type tagsCursor struct {
	repo *gitrepo.Repo
	rows []tagRow
	pos  int
}

func (c *tagsCursor) Filter(_ int, _ string, _ []fdw.Value) error {
	c.rows, c.pos = nil, 0
	g := c.repo.Git()
	iter, err := g.Tags()
	if err != nil {
		return err
	}
	defer iter.Close()
	return iter.ForEach(func(ref *plumbing.Reference) error {
		name := ref.Name()
		row := tagRow{name: name.Short(), full: name.String()}
		if tag, err := g.TagObject(ref.Hash()); err == nil {
			row.typ = "annotated"
			row.tagHash = tag.Hash.String()
			row.taggerName = tag.Tagger.Name
			row.taggerEmail = tag.Tagger.Email
			row.taggerWhen = wallClock(tag.Tagger.When)
			row.taggerUnix = tag.Tagger.When.Unix()
			row.message = strings.TrimRight(tag.Message, "\n")
			row.hasTagger = true
			if commit, err := tag.Commit(); err == nil {
				row.target = commit.Hash.String()
			} else {
				row.target = tag.Target.String()
			}
		} else {
			row.typ = "lightweight"
			row.target = ref.Hash().String()
		}
		c.rows = append(c.rows, row)
		return nil
	})
}

func (c *tagsCursor) Next() error { c.pos++; return nil }
func (c *tagsCursor) EOF() bool   { return c.pos >= len(c.rows) }

func (c *tagsCursor) Column(n int) (fdw.Value, error) {
	r := c.rows[c.pos]
	switch n {
	case 0:
		return text(r.name), nil
	case 1:
		return text(r.full), nil
	case 2:
		return text(r.typ), nil
	case 3:
		return text(r.target), nil
	case 4:
		return textOrNull(r.taggerName), nil
	case 5:
		return textOrNull(r.taggerEmail), nil
	case 6:
		if !r.hasTagger {
			return fdw.NullValue(), nil
		}
		return text(r.taggerWhen), nil
	case 7:
		if !r.hasTagger {
			return fdw.NullValue(), nil
		}
		return intval(r.taggerUnix), nil
	case 8:
		return textOrNull(r.message), nil
	case 9:
		return textOrNull(r.tagHash), nil
	}
	return fdw.NullValue(), nil
}

func (c *tagsCursor) RowID() (int64, error) { return int64(c.pos + 1), nil }
func (c *tagsCursor) Close() error          { return nil }

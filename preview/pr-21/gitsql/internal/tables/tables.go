// Package tables implements the git-backed SQLite virtual tables.
//
// Each table is an [fdw.Source] whose rows come from a go-git repository
// resolved through a [gitrepo.Manager]. Tables are registered once per process
// (module registration in the modernc backend is process-global) and then
// instantiated for a specific repository with
//
//	CREATE VIRTUAL TABLE <name> USING <module>('<repo-spec>')
//
// where <repo-spec> is a local path, a clone URL, or an "owner/repo" GitHub
// shorthand. [CreateAll] wires up the friendly table names (commits, refs, ...)
// for one default repository.
package tables

import (
	"database/sql"
	"errors"
	"fmt"
	"strconv"
	"strings"
	"sync"
	"time"

	fdw "github.com/values-conflict/go-sqlite-fdw"
	"github.com/values-conflict/go-sqlite-fdw/modernc"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
)

// mgr is the process-wide repository manager used by every table factory. It is
// set by [Init] before any table is created.
var mgr *gitrepo.Manager

// Init sets the repository manager used to resolve repo specs.
func Init(m *gitrepo.Manager) { mgr = m }

// def describes one virtual table: its SQLite module name, the friendly table
// name created for the default repo, the CREATE TABLE schema, and the factory.
type def struct {
	module   string
	friendly string
	schema   string
	factory  fdw.ConnectFactory
}

// registry is the full set of tables, populated by each table file's init.
var registry []def

func add(d def) { registry = append(registry, d) }

var (
	regOnce sync.Once
	regErr  error
)

// Register registers every git virtual table module on the modernc driver. It
// is idempotent: module registration is process-global, so repeated calls after
// the first are no-ops.
func Register(db *sql.DB) error {
	regOnce.Do(func() {
		for _, d := range registry {
			if err := modernc.Register(db, d.module, d.factory, d.factory); err != nil {
				regErr = fmt.Errorf("register %s: %w", d.module, err)
				return
			}
		}
	})
	return regErr
}

// CreateAll creates the friendly virtual tables (commits, refs, tags, files,
// commit_files, blame) bound to spec on db.
func CreateAll(db *sql.DB, spec string) error {
	for _, d := range registry {
		stmt := fmt.Sprintf("CREATE VIRTUAL TABLE IF NOT EXISTS %s USING %s(%s)", d.friendly, d.module, sqlQuote(spec))
		if _, err := db.Exec(stmt); err != nil {
			return fmt.Errorf("create %s: %w", d.friendly, err)
		}
	}
	return nil
}

// TableNames returns the friendly names of all registered tables.
func TableNames() []string {
	out := make([]string, len(registry))
	for i, d := range registry {
		out[i] = d.friendly
	}
	return out
}

// Schemas returns the CREATE TABLE schema strings keyed by friendly name.
func Schemas() map[string]string {
	out := map[string]string{}
	for _, d := range registry {
		out[d.friendly] = d.schema
	}
	return out
}

// resolveSpec resolves the repo spec from CREATE VIRTUAL TABLE arguments.
func resolveSpec(args fdw.ConnectArgs) (*gitrepo.Repo, error) {
	if mgr == nil {
		return nil, errors.New("gitsql: repository manager not initialized")
	}
	if len(args.Args) == 0 || unquote(args.Args[0]) == "" {
		return nil, errors.New("gitsql: no repository given; use USING <module>('<repo>')")
	}
	return mgr.Resolve(unquote(args.Args[0]))
}

// --- query-planning helpers --------------------------------------------------

// eqFilter pushes down usable equality constraints on the given indexable
// columns, recording which columns were pushed (in arg order) in IdxStr so that
// [parseFilters] can map Filter args back to columns. Columns listed in omit are
// reported to SQLite as fully handled; columns listed in unique mark the scan as
// visiting at most one row.
func eqFilter(info *fdw.IndexInfo, indexable, omit, unique map[int]bool) {
	info.ConstraintUsage = make([]fdw.IndexConstraintUsage, len(info.Constraints))
	var cols []string
	arg := 1
	for i, c := range info.Constraints {
		if !c.Usable || c.Op != fdw.OpEQ || !indexable[c.Column] {
			continue
		}
		info.ConstraintUsage[i] = fdw.IndexConstraintUsage{ArgvIndex: arg, Omit: omit[c.Column]}
		cols = append(cols, strconv.Itoa(c.Column))
		if unique[c.Column] {
			info.IdxFlags |= fdw.IndexScanUnique
			info.EstimatedCost = 1
			info.EstimatedRows = 1
		}
		arg++
	}
	info.IdxStr = strings.Join(cols, ",")
}

// parseFilters maps Filter args back to the column indices recorded in idxStr.
func parseFilters(idxStr string, args []fdw.Value) map[int]fdw.Value {
	m := map[int]fdw.Value{}
	if idxStr == "" {
		return m
	}
	for i, s := range strings.Split(idxStr, ",") {
		if i >= len(args) {
			break
		}
		if col, err := strconv.Atoi(s); err == nil {
			m[col] = args[i]
		}
	}
	return m
}

// filterText returns the text value of a pushed-down filter on column col.
func filterText(f map[int]fdw.Value, col int) (string, bool) {
	v, ok := f[col]
	if !ok || v.Type() != fdw.Text {
		return "", false
	}
	return v.Text(), true
}

// --- value helpers -----------------------------------------------------------

func text(s string) fdw.Value {
	return fdw.TextValue(s)
}

func textOrNull(s string) fdw.Value {
	if s == "" {
		return fdw.NullValue()
	}
	return fdw.TextValue(s)
}

func intval(i int64) fdw.Value { return fdw.IntValue(i) }

func boolval(b bool) fdw.Value {
	if b {
		return fdw.IntValue(1)
	}
	return fdw.IntValue(0)
}

// wallClock formats a time as the author's local wall-clock with no zone, so
// SQLite date functions (e.g. strftime('%H', author_when)) report the hour the
// author actually saw on their clock rather than UTC.
func wallClock(t time.Time) string {
	return t.Format("2006-01-02T15:04:05")
}

// --- small string helpers ----------------------------------------------------

// unquote strips a single layer of matching surrounding quotes if present, as
// SQLite passes CREATE VIRTUAL TABLE arguments verbatim including quotes.
func unquote(s string) string {
	s = strings.TrimSpace(s)
	if len(s) >= 2 {
		if (s[0] == '\'' && s[len(s)-1] == '\'') || (s[0] == '"' && s[len(s)-1] == '"') {
			return s[1 : len(s)-1]
		}
	}
	return s
}

// sqlQuote wraps s as a single-quoted SQL string literal.
func sqlQuote(s string) string {
	return "'" + strings.ReplaceAll(s, "'", "''") + "'"
}

// firstLine returns the first line of s, trimmed.
func firstLine(s string) string {
	if i := strings.IndexByte(s, '\n'); i >= 0 {
		return strings.TrimSpace(s[:i])
	}
	return strings.TrimSpace(s)
}

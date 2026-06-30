// Package tables wires the registry client into SQLite as a set of read-only
// virtual tables, using the go-sqlite-fdw framework on the modernc backend.
//
// Every table takes its registry coordinates through HIDDEN columns that must
// be constrained with `=` in the query (e.g. WHERE reference = 'nginx'). This
// mirrors SQLite's own table-valued functions and keeps us from ever trying to
// enumerate an entire registry. Tables that resolve to a single image accept an
// optional `platform` HIDDEN column (default linux/amd64).
package tables

import (
	"database/sql"
	"encoding/json"
	"fmt"
	"strings"
	"sync/atomic"
	"time"

	fdw "github.com/values-conflict/go-sqlite-fdw"
	"github.com/values-conflict/go-sqlite-fdw/modernc"

	"github.com/imjasonh/playground/ocidb/internal/registry"
)

// installSeq makes module names unique per Install call. modernc's module
// registry is process-global and rejects duplicate names, so binding a fresh
// internal module name per call lets each database (and each test) install its
// own modules bound to its own client without clashing.
var installSeq atomic.Int64

// Install registers every virtual-table module and creates the friendly-named
// tables (tags, manifest, ...) on db.
//
// modernc registers modules globally and only applies them to connections
// opened after registration, so we register all modules first and create the
// tables afterwards. Pin db to a single connection (SetMaxOpenConns(1)) before
// calling Install so the created tables stay visible.
func Install(db *sql.DB, client *registry.Client) error {
	seq := installSeq.Add(1)
	module := func(name string) string { return fmt.Sprintf("ocidb_%s_%d", name, seq) }

	for i := range defs {
		def := &defs[i]
		factory := func(fdw.ConnectArgs) (fdw.Source, string, error) {
			return &source{def: def, client: client}, def.schema, nil
		}
		if err := modernc.Register(db, module(def.name), nil, factory); err != nil {
			return fmt.Errorf("register module %q: %w", def.name, err)
		}
	}
	for _, def := range defs {
		if _, err := db.Exec(fmt.Sprintf("CREATE VIRTUAL TABLE IF NOT EXISTS %s USING %s()", def.name, module(def.name))); err != nil {
			return fmt.Errorf("create table %q: %w", def.name, err)
		}
	}
	return nil
}

// Names returns the virtual-table names in display order.
func Names() []string {
	out := make([]string, len(defs))
	for i, d := range defs {
		out[i] = d.name
	}
	return out
}

// Schema returns the CREATE TABLE declaration for a named table, or "".
func Schema(name string) string {
	for _, d := range defs {
		if d.name == name {
			return d.schema
		}
	}
	return ""
}

// param is a HIDDEN input column that must be supplied via `col = value`.
type param struct {
	name     string
	col      int
	required bool
}

// tableDef describes one virtual table.
type tableDef struct {
	name   string
	schema string
	params []param
	fetch  func(c *registry.Client, args map[string]string) ([]fdw.Row, error)
}

func (d *tableDef) paramByCol(col int) *param {
	for i := range d.params {
		if d.params[i].col == col {
			return &d.params[i]
		}
	}
	return nil
}

// source is the fdw.Source for every table; behaviour is driven by its def.
type source struct {
	def    *tableDef
	client *registry.Client
}

func (s *source) BestIndex(info *fdw.IndexInfo) error {
	info.ConstraintUsage = make([]fdw.IndexConstraintUsage, len(info.Constraints))
	var order []string
	seen := map[int]bool{}
	argv := 1
	for i, c := range info.Constraints {
		if !c.Usable || c.Op != fdw.OpEQ {
			continue
		}
		p := s.def.paramByCol(c.Column)
		if p == nil || seen[p.col] {
			continue
		}
		info.ConstraintUsage[i] = fdw.IndexConstraintUsage{ArgvIndex: argv, Omit: true}
		order = append(order, p.name)
		seen[p.col] = true
		argv++
	}
	info.IdxStr = strings.Join(order, ",")
	// These tables hit the network, so a scan that leaves HIDDEN parameters
	// unbound is ruinously expensive. Crucially, the cost must keep dropping as
	// we push down *more* equality constraints: otherwise, for a join like
	// `layers.platform = plats.platform`, the planner may pick a join order that
	// only binds `reference` and leaves `platform` to be post-filtered -- which
	// silently falls back to the default platform. Dividing the cost per pushed
	// constraint makes the planner prefer the order that binds every parameter.
	cost := 1e12
	for range order {
		cost /= 1000
	}
	info.EstimatedCost = cost
	if len(order) == 0 {
		info.EstimatedRows = 1_000_000
	} else {
		info.EstimatedRows = 16
	}
	return nil
}

func (s *source) Open() (fdw.Cursor, error) {
	return &cursor{def: s.def, client: s.client}, nil
}

func (s *source) Disconnect() error { return nil }
func (s *source) Destroy() error    { return nil }

// cursor materializes all rows in Filter, then iterates them.
type cursor struct {
	def    *tableDef
	client *registry.Client
	rows   []fdw.Row
	pos    int
}

func (c *cursor) Filter(_ int, idxStr string, args []fdw.Value) error {
	c.rows = nil
	c.pos = 0

	params := map[string]string{}
	if idxStr != "" {
		for i, nm := range strings.Split(idxStr, ",") {
			if i < len(args) {
				params[nm] = args[i].Text()
			}
		}
	}
	for _, p := range c.def.params {
		if p.required && params[p.name] == "" {
			return fmt.Errorf("%s: %q is required; add WHERE %s = '...' to your query", c.def.name, p.name, p.name)
		}
	}

	rows, err := c.def.fetch(c.client, params)
	if err != nil {
		return err
	}
	c.rows = rows
	return nil
}

func (c *cursor) Next() error { c.pos++; return nil }
func (c *cursor) EOF() bool   { return c.pos >= len(c.rows) }

func (c *cursor) Column(n int) (fdw.Value, error) {
	if c.pos >= len(c.rows) || n < 0 || n >= len(c.rows[c.pos]) {
		return fdw.NullValue(), nil
	}
	return c.rows[c.pos][n], nil
}

func (c *cursor) RowID() (int64, error) { return int64(c.pos + 1), nil }
func (c *cursor) Close() error          { return nil }

// --- value helpers ----------------------------------------------------------

func text(s string) fdw.Value { return fdw.TextValue(s) }

func nullableText(s string) fdw.Value {
	if s == "" {
		return fdw.NullValue()
	}
	return fdw.TextValue(s)
}

func intVal(n int64) fdw.Value { return fdw.IntValue(n) }

func boolVal(b bool) fdw.Value {
	if b {
		return fdw.IntValue(1)
	}
	return fdw.IntValue(0)
}

func timeVal(t time.Time) fdw.Value {
	if t.IsZero() {
		return fdw.NullValue()
	}
	return fdw.TextValue(t.UTC().Format(time.RFC3339))
}

// jsonArray renders a string slice as a compact JSON array, or NULL if empty.
func jsonArray(items []string) fdw.Value {
	if len(items) == 0 {
		return fdw.NullValue()
	}
	b, err := json.Marshal(items)
	if err != nil {
		return fdw.NullValue()
	}
	return fdw.TextValue(string(b))
}

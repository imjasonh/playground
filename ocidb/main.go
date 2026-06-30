// Command ocidb explores OCI container images in a registry (Docker Hub by
// default) through SQL, by exposing go-containerregistry as a set of SQLite
// virtual tables. Everything it fetches is cached on disk to stay friendly with
// registry rate limits.
//
// Usage:
//
//	ocidb query "SELECT tag FROM tags WHERE repository = 'library/nginx'"
//	ocidb shell
//	ocidb demo
//	ocidb schema [table]
package main

import (
	"bufio"
	"context"
	"database/sql"
	"embed"
	"encoding/csv"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/signal"
	"path/filepath"
	"sort"
	"strings"
	"text/tabwriter"
	"time"

	_ "modernc.org/sqlite"

	"github.com/imjasonh/playground/ocidb/internal/registry"
	"github.com/imjasonh/playground/ocidb/internal/tables"
)

//go:embed queries/*.sql
var queryFS embed.FS

func main() {
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, "ocidb:", err)
		os.Exit(1)
	}
}

func run(args []string) error {
	if len(args) == 0 {
		usage(os.Stderr)
		return errors.New("a subcommand is required")
	}
	cmd, rest := args[0], args[1:]
	switch cmd {
	case "query", "q":
		return cmdQuery(rest)
	case "shell", "repl":
		return cmdShell(rest)
	case "demo":
		return cmdDemo(rest)
	case "schema", "tables":
		return cmdSchema(rest)
	case "help", "-h", "--help":
		usage(os.Stdout)
		return nil
	default:
		usage(os.Stderr)
		return fmt.Errorf("unknown subcommand %q", cmd)
	}
}

func usage(w io.Writer) {
	fmt.Fprint(w, `ocidb: explore OCI images in a registry with SQL

Usage:
  ocidb query  [flags] "SELECT ..."   run a single SQL query
  ocidb shell  [flags]                interactive SQL prompt (reads stdin)
  ocidb demo   [flags]                run a tour of fun Docker Hub queries
  ocidb schema [table]                print virtual-table schema(s)

Common flags:
  --cache DIR        cache directory (default: <user-cache>/ocidb)
  --ttl DURATION     freshness window for tag lists & tag->digest (default 6h)
  --format FORMAT    table | csv | json (default table)

Tables: `+strings.Join(tables.Names(), ", ")+`

Each table takes its target through HIDDEN columns constrained with '=', e.g.
  WHERE reference = 'nginx'           (image / index reference)
  WHERE repository = 'library/nginx'  (for the tags table)
  WHERE platform = 'linux/arm64'      (optional; default linux/amd64)
`)
}

// sharedFlags holds the flags common to query/shell/demo.
type sharedFlags struct {
	cache  string
	ttl    time.Duration
	format string
}

func newFlagSet(name string) *flag.FlagSet {
	fs := flag.NewFlagSet(name, flag.ContinueOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: ocidb %s [flags] ...\n", name)
		fs.PrintDefaults()
	}
	return fs
}

func registerShared(fs *flag.FlagSet, s *sharedFlags) {
	fs.StringVar(&s.cache, "cache", defaultCacheDir(), "cache directory")
	fs.DurationVar(&s.ttl, "ttl", registry.DefaultTTL, "freshness window for mutable lookups")
	fs.StringVar(&s.format, "format", "table", "output format: table|csv|json")
}

func (s *sharedFlags) open() (*sql.DB, *registry.Client, error) {
	client, err := registry.New(registry.Options{
		Dir:       s.cache,
		TTL:       s.ttl,
		Context:   context.Background(),
		UserAgent: "ocidb/0.1 (+https://github.com/imjasonh/playground)",
	})
	if err != nil {
		return nil, nil, err
	}
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		return nil, nil, fmt.Errorf("open sqlite: %w", err)
	}
	// modernc's :memory: database is per-connection; pin to one connection so
	// the virtual tables we create stay visible.
	db.SetMaxOpenConns(1)
	if err := tables.Install(db, client); err != nil {
		db.Close()
		return nil, nil, err
	}
	return db, client, nil
}

func cmdQuery(args []string) error {
	var s sharedFlags
	fs := newFlagSet("query")
	registerShared(fs, &s)
	if err := fs.Parse(args); err != nil {
		return err
	}
	q := strings.TrimSpace(strings.Join(fs.Args(), " "))
	if q == "" {
		return errors.New("query: provide a SQL statement, e.g. ocidb query \"SELECT tag FROM tags WHERE repository='nginx'\"")
	}
	db, client, err := s.open()
	if err != nil {
		return err
	}
	defer db.Close()
	if err := runAndPrint(os.Stdout, db, q, s.format); err != nil {
		return err
	}
	reportCache(os.Stderr, client)
	return nil
}

func cmdShell(args []string) error {
	var s sharedFlags
	fs := newFlagSet("shell")
	registerShared(fs, &s)
	if err := fs.Parse(args); err != nil {
		return err
	}
	db, client, err := s.open()
	if err != nil {
		return err
	}
	defer db.Close()

	fmt.Fprintln(os.Stderr, "ocidb shell - type SQL ending in ';'. Meta: .tables .schema [t] .help .quit")
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 0, 64*1024), 4*1024*1024)
	var buf strings.Builder
	prompt := func() { fmt.Fprint(os.Stderr, promptFor(buf.Len() > 0)) }
	prompt()
	for sc.Scan() {
		line := sc.Text()
		trimmed := strings.TrimSpace(line)
		if buf.Len() == 0 && strings.HasPrefix(trimmed, ".") {
			if done := metaCommand(os.Stdout, trimmed); done {
				return nil
			}
			prompt()
			continue
		}
		buf.WriteString(line)
		buf.WriteByte('\n')
		if strings.HasSuffix(trimmed, ";") {
			stmt := strings.TrimSpace(buf.String())
			buf.Reset()
			stmt = strings.TrimSuffix(stmt, ";")
			if strings.TrimSpace(stmt) != "" {
				if err := runAndPrint(os.Stdout, db, stmt, s.format); err != nil {
					fmt.Fprintln(os.Stderr, "error:", err)
				}
			}
		}
		prompt()
	}
	if err := sc.Err(); err != nil {
		return err
	}
	reportCache(os.Stderr, client)
	return nil
}

func promptFor(continuation bool) string {
	if continuation {
		return "  ...> "
	}
	return "ocidb> "
}

func metaCommand(w io.Writer, line string) (done bool) {
	fields := strings.Fields(line)
	switch fields[0] {
	case ".quit", ".exit", ".q":
		return true
	case ".tables":
		fmt.Fprintln(w, strings.Join(tables.Names(), "\n"))
	case ".schema":
		if len(fields) > 1 {
			fmt.Fprintln(w, displaySchema(tables.Schema(fields[1])))
		} else {
			for _, n := range tables.Names() {
				fmt.Fprintln(w, displaySchema(tables.Schema(n))+";")
			}
		}
	case ".help":
		fmt.Fprintln(w, ".tables          list virtual tables")
		fmt.Fprintln(w, ".schema [table]  show CREATE TABLE for a table (or all)")
		fmt.Fprintln(w, ".quit            exit")
	default:
		fmt.Fprintf(w, "unknown meta-command %q (try .help)\n", fields[0])
	}
	return false
}

func cmdSchema(args []string) error {
	if len(args) == 0 {
		for _, n := range tables.Names() {
			fmt.Println(displaySchema(tables.Schema(n)) + ";")
			fmt.Println()
		}
		return nil
	}
	s := tables.Schema(args[0])
	if s == "" {
		return fmt.Errorf("unknown table %q (have: %s)", args[0], strings.Join(tables.Names(), ", "))
	}
	fmt.Println(displaySchema(s) + ";")
	return nil
}

// displaySchema reformats a stored CREATE TABLE string (which carries Go source
// indentation) into a tidy, evenly-indented form for display.
func displaySchema(s string) string {
	var out []string
	for _, line := range strings.Split(s, "\n") {
		t := strings.TrimSpace(line)
		if t == "" {
			continue
		}
		if strings.HasPrefix(t, "CREATE TABLE") || strings.HasPrefix(t, ")") {
			out = append(out, t)
		} else {
			out = append(out, "  "+t)
		}
	}
	return strings.Join(out, "\n")
}

func cmdDemo(args []string) error {
	var s sharedFlags
	var list bool
	fs := newFlagSet("demo")
	registerShared(fs, &s)
	fs.BoolVar(&list, "list", false, "print the demo queries without running them")
	if err := fs.Parse(args); err != nil {
		return err
	}

	demos, err := loadQueries()
	if err != nil {
		return err
	}
	if list {
		for _, d := range demos {
			fmt.Printf("-- %s\n%s\n\n", d.title, d.sql)
		}
		return nil
	}

	db, client, err := s.open()
	if err != nil {
		return err
	}
	defer db.Close()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt)
	defer stop()

	for i, d := range demos {
		if ctx.Err() != nil {
			break
		}
		fmt.Printf("\n\033[1m== %d/%d  %s\033[0m\n", i+1, len(demos), d.title)
		fmt.Printf("\033[2m%s\033[0m\n", d.sql)
		if err := runAndPrint(os.Stdout, db, d.sql, s.format); err != nil {
			fmt.Fprintln(os.Stderr, "  query failed:", err)
		}
	}
	reportCache(os.Stderr, client)
	return nil
}

type demoQuery struct {
	title string
	sql   string
}

// loadQueries reads the embedded queries/*.sql files. The leading comment lines
// (starting with --) form the title; the remainder is the SQL to run.
func loadQueries() ([]demoQuery, error) {
	entries, err := fs.ReadDir(queryFS, "queries")
	if err != nil {
		return nil, err
	}
	names := make([]string, 0, len(entries))
	for _, e := range entries {
		if !e.IsDir() && strings.HasSuffix(e.Name(), ".sql") {
			names = append(names, e.Name())
		}
	}
	sort.Strings(names)

	var out []demoQuery
	for _, n := range names {
		b, err := queryFS.ReadFile(filepath.ToSlash(filepath.Join("queries", n)))
		if err != nil {
			return nil, err
		}
		title, sqlText := splitQueryFile(string(b))
		if title == "" {
			title = strings.TrimSuffix(n, ".sql")
		}
		if strings.TrimSpace(sqlText) != "" {
			out = append(out, demoQuery{title: title, sql: strings.TrimSpace(sqlText)})
		}
	}
	return out, nil
}

func splitQueryFile(content string) (title, sqlText string) {
	var titleParts, sqlParts []string
	inBody := false
	for _, line := range strings.Split(content, "\n") {
		if !inBody && strings.HasPrefix(strings.TrimSpace(line), "--") {
			titleParts = append(titleParts, strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(line), "--")))
			continue
		}
		inBody = true
		sqlParts = append(sqlParts, line)
	}
	return strings.TrimSpace(strings.Join(titleParts, " ")), strings.TrimSpace(strings.Join(sqlParts, "\n"))
}

// --- query execution + output ----------------------------------------------

func runAndPrint(w io.Writer, db *sql.DB, query, format string) error {
	rows, err := db.Query(query)
	if err != nil {
		return err
	}
	defer rows.Close()
	cols, err := rows.Columns()
	if err != nil {
		return err
	}
	var data [][]any
	for rows.Next() {
		cells := make([]any, len(cols))
		ptrs := make([]any, len(cols))
		for i := range cells {
			ptrs[i] = &cells[i]
		}
		if err := rows.Scan(ptrs...); err != nil {
			return err
		}
		data = append(data, cells)
	}
	if err := rows.Err(); err != nil {
		return err
	}

	switch format {
	case "json":
		return printJSON(w, cols, data)
	case "csv":
		return printCSV(w, cols, data)
	case "table", "":
		return printTable(w, cols, data)
	default:
		return fmt.Errorf("unknown format %q (table|csv|json)", format)
	}
}

func printTable(w io.Writer, cols []string, data [][]any) error {
	tw := tabwriter.NewWriter(w, 0, 4, 2, ' ', 0)
	fmt.Fprintln(tw, strings.Join(cols, "\t"))
	seps := make([]string, len(cols))
	for i, c := range cols {
		seps[i] = strings.Repeat("-", max(len(c), 3))
	}
	fmt.Fprintln(tw, strings.Join(seps, "\t"))
	for _, row := range data {
		cells := make([]string, len(row))
		for i, v := range row {
			cells[i] = cellString(v)
		}
		fmt.Fprintln(tw, strings.Join(cells, "\t"))
	}
	if err := tw.Flush(); err != nil {
		return err
	}
	fmt.Fprintf(w, "(%d row%s)\n", len(data), plural(len(data)))
	return nil
}

func printCSV(w io.Writer, cols []string, data [][]any) error {
	cw := csv.NewWriter(w)
	if err := cw.Write(cols); err != nil {
		return err
	}
	for _, row := range data {
		rec := make([]string, len(row))
		for i, v := range row {
			rec[i] = cellString(v)
		}
		if err := cw.Write(rec); err != nil {
			return err
		}
	}
	cw.Flush()
	return cw.Error()
}

func printJSON(w io.Writer, cols []string, data [][]any) error {
	out := make([]map[string]any, 0, len(data))
	for _, row := range data {
		m := make(map[string]any, len(cols))
		for i, c := range cols {
			m[c] = jsonCell(row[i])
		}
		out = append(out, m)
	}
	enc := json.NewEncoder(w)
	enc.SetIndent("", "  ")
	return enc.Encode(out)
}

func cellString(v any) string {
	switch x := v.(type) {
	case nil:
		return ""
	case []byte:
		return string(x)
	case string:
		return x
	case int64:
		return fmt.Sprintf("%d", x)
	case float64:
		return fmt.Sprintf("%g", x)
	case bool:
		if x {
			return "1"
		}
		return "0"
	default:
		return fmt.Sprintf("%v", x)
	}
}

func jsonCell(v any) any {
	if b, ok := v.([]byte); ok {
		return string(b)
	}
	return v
}

func reportCache(w io.Writer, c *registry.Client) {
	hits, misses := c.Stats()
	if hits == 0 && misses == 0 {
		return
	}
	fmt.Fprintf(w, "\033[2m[cache] %d hit(s), %d network fetch(es)\033[0m\n", hits, misses)
}

func defaultCacheDir() string {
	if dir := os.Getenv("OCIDB_CACHE"); dir != "" {
		return dir
	}
	base, err := os.UserCacheDir()
	if err != nil || base == "" {
		return filepath.Join(os.TempDir(), "ocidb-cache")
	}
	return filepath.Join(base, "ocidb")
}

func plural(n int) string {
	if n == 1 {
		return ""
	}
	return "s"
}

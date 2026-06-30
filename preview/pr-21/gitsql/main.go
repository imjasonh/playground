// Command gitsql exposes a git repository as a set of SQLite virtual tables and
// lets you query it with SQL.
//
// It wires go-git (repository access, cloned and cached locally) to a SQLite
// virtual-table framework (github.com/values-conflict/go-sqlite-fdw) running on
// the pure-Go modernc.org/sqlite engine -- no CGo, no system SQLite.
//
// Usage:
//
//	gitsql [flags] [repo] [sql]
//
// repo is a local path, a clone URL, or an "owner/repo" GitHub shorthand
// (default "."). With no SQL it opens an interactive prompt.
package main

import (
	"database/sql"
	"embed"
	"flag"
	"fmt"
	"io"
	"os"
	"path"
	"sort"
	"strings"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
	"github.com/imjasonh/playground/gitsql/internal/tables"
)

//go:embed queries/*.sql
var exampleFS embed.FS

func main() {
	if err := run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr); err != nil {
		fmt.Fprintln(os.Stderr, "gitsql:", err)
		os.Exit(1)
	}
}

func run(argv []string, stdin io.Reader, stdout, stderr io.Writer) error {
	fs := flag.NewFlagSet("gitsql", flag.ContinueOnError)
	fs.SetOutput(stderr)
	var (
		query        = fs.String("query", "", "SQL to run (alias: -q)")
		queryShort   = fs.String("q", "", "SQL to run")
		file         = fs.String("file", "", "read SQL from a file (- for stdin)")
		example      = fs.String("example", "", "run a built-in example query by name")
		listExamples = fs.Bool("list-examples", false, "list the built-in example queries and exit")
		format       = fs.String("format", "table", "output format: table, csv, tsv, json, md")
		cacheDir     = fs.String("cache", "", "cache directory for cloned repos (default: <user cache>/gitsql)")
		offline      = fs.Bool("offline", false, "never hit the network; require a cached clone")
		update       = fs.Bool("update", false, "fetch new commits for a cached repo before querying")
		schema       = fs.Bool("schema", false, "print the schema of every table and exit")
		maxWidth     = fs.Int("max-width", 60, "truncate table cells to this width (0 = unlimited)")
		quiet        = fs.Bool("quiet", false, "suppress clone/fetch progress output")
	)
	fs.Usage = func() {
		fmt.Fprintf(stderr, "usage: gitsql [flags] [repo] [sql]\n\n"+
			"repo is a local path, clone URL, or owner/repo (default \".\").\n"+
			"With no SQL, gitsql opens an interactive prompt.\n\nflags:\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(argv); err != nil {
		return err
	}

	if *listExamples {
		return printExampleList(stdout)
	}
	if *schema {
		return printSchemas(stdout)
	}

	q := firstNonEmpty(*query, *queryShort)

	args := fs.Args()
	repo := "."
	if len(args) >= 1 {
		repo = args[0]
	}
	if q == "" && len(args) >= 2 {
		q = strings.Join(args[1:], " ")
	}

	if *example != "" {
		body, err := loadExample(*example)
		if err != nil {
			return err
		}
		q = body
	} else if *file != "" {
		body, err := readFile(*file, stdin)
		if err != nil {
			return err
		}
		q = body
	}

	var progress io.Writer
	if !*quiet {
		progress = stderr
	}
	mgr, err := gitrepo.NewManager(gitrepo.Options{
		CacheDir: *cacheDir,
		Offline:  *offline,
		Update:   *update,
		Progress: progress,
	})
	if err != nil {
		return err
	}
	tables.Init(mgr)

	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		return err
	}
	defer db.Close()
	db.SetMaxOpenConns(1) // an in-memory DB lives on a single connection

	if err := tables.Register(db); err != nil {
		return err
	}
	if err := tables.CreateAll(db, repo); err != nil {
		return err
	}

	printer := &printer{format: *format, maxWidth: *maxWidth}

	// Non-interactive: query came from -q/-file/-example/positional or piped stdin.
	if q == "" && !isTerminal(stdin) {
		body, err := io.ReadAll(stdin)
		if err != nil {
			return err
		}
		q = string(body)
	}
	if q != "" {
		return runScript(db, q, printer, stdout)
	}

	return repl(db, repo, mgr, printer, stdin, stdout, stderr)
}

func firstNonEmpty(vals ...string) string {
	for _, v := range vals {
		if v != "" {
			return v
		}
	}
	return ""
}

func readFile(name string, stdin io.Reader) (string, error) {
	if name == "-" {
		b, err := io.ReadAll(stdin)
		return string(b), err
	}
	b, err := os.ReadFile(name)
	return string(b), err
}

// runScript executes one or more ';'-separated statements, printing the results
// of each.
func runScript(db *sql.DB, script string, p *printer, w io.Writer) error {
	for _, stmt := range splitStatements(script) {
		if err := runOne(db, stmt, p, w); err != nil {
			return fmt.Errorf("%w\n  in: %s", err, oneLine(stmt))
		}
	}
	return nil
}

func runOne(db *sql.DB, stmt string, p *printer, w io.Writer) error {
	stmt = strings.TrimSpace(stmt)
	if stmt == "" {
		return nil
	}
	rows, err := db.Query(stmt)
	if err != nil {
		return err
	}
	defer rows.Close()
	cols, err := rows.Columns()
	if err != nil {
		return err
	}
	if len(cols) == 0 {
		// Statement with no result set (e.g. CREATE VIRTUAL TABLE); nothing to print.
		return rows.Err()
	}
	var data [][]any
	for rows.Next() {
		cell := make([]any, len(cols))
		ptr := make([]any, len(cols))
		for i := range cell {
			ptr[i] = &cell[i]
		}
		if err := rows.Scan(ptr...); err != nil {
			return err
		}
		data = append(data, cell)
	}
	if err := rows.Err(); err != nil {
		return err
	}
	return p.print(w, cols, data)
}

// splitStatements splits a script on semicolons that are not inside string
// literals or line comments. It is deliberately simple but handles the SQL this
// tool emits and the bundled examples.
func splitStatements(script string) []string {
	var out []string
	var b strings.Builder
	var inSingle, inDouble, inLineComment bool
	for i := 0; i < len(script); i++ {
		c := script[i]
		switch {
		case inLineComment:
			b.WriteByte(c)
			if c == '\n' {
				inLineComment = false
			}
			continue
		case inSingle:
			b.WriteByte(c)
			if c == '\'' {
				inSingle = false
			}
			continue
		case inDouble:
			b.WriteByte(c)
			if c == '"' {
				inDouble = false
			}
			continue
		}
		switch c {
		case '\'':
			inSingle = true
		case '"':
			inDouble = true
		case '-':
			if i+1 < len(script) && script[i+1] == '-' {
				inLineComment = true
			}
		case ';':
			out = append(out, b.String())
			b.Reset()
			continue
		}
		b.WriteByte(c)
	}
	if rest := strings.TrimSpace(b.String()); rest != "" {
		out = append(out, b.String())
	}
	return out
}

func oneLine(s string) string {
	s = strings.TrimSpace(s)
	s = strings.Join(strings.Fields(s), " ")
	if len(s) > 120 {
		s = s[:117] + "..."
	}
	return s
}

// --- examples ----------------------------------------------------------------

type example struct {
	name  string
	title string
	body  string
}

func loadExamples() ([]example, error) {
	entries, err := exampleFS.ReadDir("queries")
	if err != nil {
		return nil, err
	}
	var out []example
	for _, e := range entries {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".sql") {
			continue
		}
		body, err := exampleFS.ReadFile(path.Join("queries", e.Name()))
		if err != nil {
			return nil, err
		}
		out = append(out, example{
			name:  strings.TrimSuffix(e.Name(), ".sql"),
			title: exampleTitle(string(body)),
			body:  string(body),
		})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].name < out[j].name })
	return out, nil
}

func exampleTitle(body string) string {
	for _, line := range strings.Split(body, "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "--") {
			return strings.TrimSpace(strings.TrimPrefix(line, "--"))
		}
		if line != "" {
			break
		}
	}
	return ""
}

func loadExample(name string) (string, error) {
	exs, err := loadExamples()
	if err != nil {
		return "", err
	}
	for _, e := range exs {
		if e.name == name {
			return e.body, nil
		}
	}
	return "", fmt.Errorf("unknown example %q (try --list-examples)", name)
}

func printExampleList(w io.Writer) error {
	exs, err := loadExamples()
	if err != nil {
		return err
	}
	width := 0
	for _, e := range exs {
		if len(e.name) > width {
			width = len(e.name)
		}
	}
	for _, e := range exs {
		fmt.Fprintf(w, "  %-*s  %s\n", width, e.name, e.title)
	}
	return nil
}

func printSchemas(w io.Writer) error {
	schemas := tables.Schemas()
	names := tables.TableNames()
	for _, n := range names {
		fmt.Fprintln(w, strings.TrimSpace(schemas[n]))
		fmt.Fprintln(w)
	}
	return nil
}

// --- terminal detection ------------------------------------------------------

func isTerminal(r io.Reader) bool {
	f, ok := r.(*os.File)
	if !ok {
		return false
	}
	info, err := f.Stat()
	if err != nil {
		return false
	}
	return info.Mode()&os.ModeCharDevice != 0
}

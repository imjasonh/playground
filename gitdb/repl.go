package main

import (
	"bufio"
	"database/sql"
	"fmt"
	"io"
	"strings"

	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
	"github.com/imjasonh/playground/gitdb/internal/tables"
)

// repl runs an interactive SQL prompt over the registered tables.
func repl(db *sql.DB, repo string, mgr *gitrepo.Manager, p *printer, stdin io.Reader, stdout, stderr io.Writer) error {
	banner(repo, mgr, p, stdout)

	sc := bufio.NewScanner(stdin)
	sc.Buffer(make([]byte, 0, 64*1024), 4*1024*1024)
	var buf strings.Builder
	prompt(stdout, buf.Len() > 0)

	for sc.Scan() {
		line := sc.Text()
		trimmed := strings.TrimSpace(line)

		// Meta-commands are only recognized at the start of a statement.
		if buf.Len() == 0 && strings.HasPrefix(trimmed, ".") {
			if done := metaCommand(db, p, stdout, trimmed); done {
				return nil
			}
			prompt(stdout, false)
			continue
		}

		buf.WriteString(line)
		buf.WriteByte('\n')
		if strings.HasSuffix(trimmed, ";") {
			stmt := buf.String()
			buf.Reset()
			if err := runScript(db, stmt, p, stdout); err != nil {
				fmt.Fprintln(stderr, "error:", err)
			}
			prompt(stdout, false)
			continue
		}
		prompt(stdout, buf.Len() > 0)
	}
	fmt.Fprintln(stdout)
	return sc.Err()
}

func prompt(w io.Writer, cont bool) {
	if cont {
		fmt.Fprint(w, "  ...> ")
	} else {
		fmt.Fprint(w, "gitdb> ")
	}
}

func banner(repo string, mgr *gitrepo.Manager, p *printer, w io.Writer) {
	fmt.Fprintln(w, "gitdb — query a git repo with SQL (go-git + modernc SQLite vtab)")
	fmt.Fprintf(w, "repo:   %s\n", repo)
	if r, err := mgr.Resolve(repo); err == nil {
		fmt.Fprintf(w, "cache:  %s\n", r.Path)
	}
	fmt.Fprintf(w, "tables: %s\n", strings.Join(tables.TableNames(), ", "))
	fmt.Fprintln(w, "Type SQL ending in ';'. Try .help, .examples, or .quit.")
	fmt.Fprintln(w)
}

// metaCommand handles dot-commands. It returns true when the REPL should exit.
func metaCommand(db *sql.DB, p *printer, w io.Writer, cmd string) bool {
	fields := strings.Fields(cmd)
	switch fields[0] {
	case ".quit", ".exit", ".q":
		return true
	case ".help", ".h":
		fmt.Fprint(w, helpText)
	case ".tables":
		fmt.Fprintln(w, strings.Join(tables.TableNames(), "  "))
	case ".schema":
		schemas := tables.Schemas()
		if len(fields) > 1 {
			if s, ok := schemas[fields[1]]; ok {
				fmt.Fprintln(w, strings.TrimSpace(s))
			} else {
				fmt.Fprintf(w, "no such table: %s\n", fields[1])
			}
		} else {
			for _, n := range tables.TableNames() {
				fmt.Fprintln(w, strings.TrimSpace(schemas[n]))
				fmt.Fprintln(w)
			}
		}
	case ".examples":
		_ = printExampleList(w)
	case ".example":
		if len(fields) < 2 {
			fmt.Fprintln(w, "usage: .example <name>")
			break
		}
		body, err := loadExample(fields[1])
		if err != nil {
			fmt.Fprintln(w, err)
			break
		}
		fmt.Fprintln(w, strings.TrimSpace(body))
		if err := runScript(db, body, p, w); err != nil {
			fmt.Fprintln(w, "error:", err)
		}
	case ".format":
		if len(fields) < 2 {
			fmt.Fprintf(w, "format: %s\n", p.format)
			break
		}
		p.format = fields[1]
	default:
		fmt.Fprintf(w, "unknown command: %s (try .help)\n", fields[0])
	}
	return false
}

const helpText = `Commands:
  .tables             list the available tables
  .schema [table]     show CREATE TABLE for one or all tables
  .examples           list built-in example queries
  .example <name>     run a built-in example query
  .format <fmt>       set output format (table, csv, tsv, json, md)
  .help               show this help
  .quit               exit

Tables: commits, refs, tags, files, commit_files, blame.
Each table also takes an explicit repo, e.g.:
  CREATE VIRTUAL TABLE k_commits USING git_commits('imjasonh/playground');
Then JOIN across repositories.
`

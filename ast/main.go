// Command ast is a cross-language structural search-and-rewrite tool built on
// tree-sitter. It parses source in any of its supported languages, selects AST
// nodes with tree-sitter's query language, and can rewrite the matched nodes
// and write the result back to disk.
//
// Usage:
//
//	ast languages                              list supported languages
//	ast tree     [-l lang] <file>              print the syntax tree
//	ast query    -q <query> [-l lang] <file>…  print nodes matching a selector
//	ast rewrite  -q <query> [ops] [-w] <file>… edit matched nodes
//
// The selector is a tree-sitter query (an S-expression pattern with @captures),
// the same query language used by editors and the tree-sitter CLI. For example
// `(function_declaration name: (identifier) @name)` captures every Go function
// name. Run `ast tree file.go` to discover the node types to match.
package main

import (
	"errors"
	"fmt"
	"io"
	"os"
	"strings"
)

const progName = "ast"

func main() { os.Exit(astMain()) }

// astMain runs the CLI and returns a process exit code. It is separated from
// main so it can be registered as a command with testscript (see the golden
// CLI tests in scripts_test.go).
func astMain() int {
	if err := run(os.Args[1:], os.Stdout, os.Stderr); err != nil {
		fmt.Fprintln(os.Stderr, progName+":", err)
		return 1
	}
	return 0
}

func run(args []string, stdout, stderr io.Writer) error {
	if len(args) == 0 {
		usage(stderr)
		return errors.New("a subcommand is required")
	}
	cmd, rest := args[0], args[1:]
	switch cmd {
	case "languages", "langs", "lang":
		return cmdLanguages(rest, stdout)
	case "tree", "parse":
		return cmdTree(rest, stdout)
	case "query", "q", "select":
		return cmdQuery(rest, stdout)
	case "rewrite", "edit", "replace":
		return cmdRewrite(rest, stdout, stderr)
	case "help", "-h", "--help":
		usage(stdout)
		return nil
	default:
		usage(stderr)
		return fmt.Errorf("unknown subcommand %q", cmd)
	}
}

func usage(w io.Writer) {
	fmt.Fprint(w, `ast: cross-language AST search and rewrite, powered by tree-sitter

Usage:
  ast languages                                list supported languages and extensions
  ast tree     [-l lang] <file>                print the syntax tree (S-expression)
  ast query    -q QUERY [-l lang] <file>...    print AST nodes matching a selector
  ast rewrite  -q QUERY [ops] [-w] <file>...   rewrite matched nodes

The selector is a tree-sitter query, e.g.
  '(function_declaration name: (identifier) @name)'

Rewrite operations (each may be repeated; target a @capture from the query):
  --replace       @cap=TEXT   replace the captured node's text
  --delete        @cap        delete the captured node
  --insert-before @cap=TEXT   insert TEXT immediately before the node
  --insert-after  @cap=TEXT   insert TEXT immediately after the node

TEXT may interpolate other captures from the same match with {{name}}, and
understands the escapes \n, \t, \r, and \\.

Common flags:
  -l, --lang   force a language instead of inferring from the file extension
  -q, --query  the tree-sitter selector (required for query/rewrite)
      --json   machine-readable output (query, tree)
  -w, --write  write rewrites back to files instead of printing to stdout
      --diff   print a unified diff of rewrites without applying them
      --patch  write a unified diff to the given file without applying (--patch=out.patch)

Pass "-" as the file to read from stdin (requires -l).

Examples:
  ast query -q '(call_expression function: (identifier) @f)' main.go
  ast rewrite -q '((identifier) @id (#eq? @id "foo"))' --replace '@id=bar' -w *.go
`)
}

// stringSlice is a repeatable string flag.
type stringSlice []string

func (s *stringSlice) String() string { return strings.Join(*s, ",") }
func (s *stringSlice) Set(v string) error {
	*s = append(*s, v)
	return nil
}

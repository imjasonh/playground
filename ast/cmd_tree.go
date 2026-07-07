package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"strings"
	"unicode/utf8"

	sitter "github.com/smacker/go-tree-sitter"

	"github.com/imjasonh/playground/ast/internal/engine"
)

func cmdTree(args []string, stdout io.Writer) error {
	fs := flag.NewFlagSet("tree", flag.ContinueOnError)
	fs.SetOutput(stdout)
	var langName string
	fs.StringVar(&langName, "l", "", "language name (default: infer from extension)")
	fs.StringVar(&langName, "lang", "", "language name (default: infer from extension)")
	sexp := fs.Bool("sexp", false, "print the raw one-line S-expression")
	all := fs.Bool("a", false, "include anonymous (unnamed) nodes")
	fs.BoolVar(all, "all", false, "include anonymous (unnamed) nodes")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 1 {
		return fmt.Errorf("tree takes exactly one file (got %d)", fs.NArg())
	}

	src, err := loadSource(fs.Arg(0), langName, stdinReader())
	if err != nil {
		return err
	}
	tree, err := engine.Parse(context.Background(), src.data, src.sitter())
	if err != nil {
		return err
	}
	defer tree.Close()
	root := tree.RootNode()

	if *sexp {
		fmt.Fprintln(stdout, root.String())
		return nil
	}
	printTree(stdout, root, src.data, *all)
	return nil
}

// printTree writes an indented view of the syntax tree using a cursor so that
// field names (e.g. "name:", "body:") are shown.
func printTree(w io.Writer, root *sitter.Node, src []byte, includeAnon bool) {
	var walk func(n *sitter.Node, field string, depth int)
	walk = func(n *sitter.Node, field string, depth int) {
		if !includeAnon && !n.IsNamed() {
			return
		}
		indent := strings.Repeat("  ", depth)
		label := n.Type()
		if field != "" {
			label = field + ": " + label
		}
		loc := fmt.Sprintf("[%d:%d-%d:%d]",
			n.StartPoint().Row+1, n.StartPoint().Column+1,
			n.EndPoint().Row+1, n.EndPoint().Column+1)

		line := fmt.Sprintf("%s%s %s", indent, label, loc)
		// Show text for leaves so the tree is self-explanatory.
		if n.NamedChildCount() == 0 {
			if txt := oneLine(n.Content(src)); txt != "" {
				line += "  " + txt
			}
		}
		fmt.Fprintln(w, line)

		cursor := sitter.NewTreeCursor(n)
		defer cursor.Close()
		if !cursor.GoToFirstChild() {
			return
		}
		for {
			child := cursor.CurrentNode()
			walk(child, cursor.CurrentFieldName(), depth+1)
			if !cursor.GoToNextSibling() {
				break
			}
		}
	}
	walk(root, "", 0)
}

// oneLine collapses a node's text to a compact single-line quoted form for
// display.
func oneLine(s string) string {
	s = strings.TrimSpace(s)
	if s == "" {
		return ""
	}
	if i := strings.IndexAny(s, "\r\n"); i >= 0 {
		s = strings.TrimRight(s[:i], " \t") + " …"
	}
	const max = 60
	if utf8.RuneCountInString(s) > max {
		s = string([]rune(s)[:max]) + "…"
	}
	return fmt.Sprintf("%q", s)
}

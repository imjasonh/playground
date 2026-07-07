package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"regexp"
	"strings"

	"github.com/imjasonh/playground/ast/internal/engine"
)

// op is a single rewrite operation targeting a query capture.
type op struct {
	kind    opKind
	capture string
	text    string
}

type opKind int

const (
	opReplace opKind = iota
	opDelete
	opInsertBefore
	opInsertAfter
)

func cmdRewrite(args []string, stdout, stderr io.Writer) error {
	fs := flag.NewFlagSet("rewrite", flag.ContinueOnError)
	fs.SetOutput(stdout)
	var (
		langName                                       string
		query                                          string
		replaces, deletes, insertsBefore, insertsAfter stringSlice
		write, diff                                    bool
	)
	fs.StringVar(&langName, "l", "", "language name (default: infer from extension)")
	fs.StringVar(&langName, "lang", "", "language name (default: infer from extension)")
	fs.StringVar(&query, "q", "", "tree-sitter query selector (required)")
	fs.StringVar(&query, "query", "", "tree-sitter query selector (required)")
	fs.Var(&replaces, "replace", "@cap=TEXT: replace the captured node (repeatable)")
	fs.Var(&deletes, "delete", "@cap: delete the captured node (repeatable)")
	fs.Var(&insertsBefore, "insert-before", "@cap=TEXT: insert before the node (repeatable)")
	fs.Var(&insertsAfter, "insert-after", "@cap=TEXT: insert after the node (repeatable)")
	fs.BoolVar(&write, "w", false, "write changes back to files")
	fs.BoolVar(&write, "write", false, "write changes back to files")
	fs.BoolVar(&diff, "diff", false, "print a unified diff instead of the result")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if query == "" {
		return fmt.Errorf("rewrite requires -q/--query")
	}
	if fs.NArg() == 0 {
		return fmt.Errorf("rewrite requires at least one file (or - for stdin)")
	}

	ops, err := parseOps(replaces, deletes, insertsBefore, insertsAfter)
	if err != nil {
		return err
	}
	if len(ops) == 0 {
		return fmt.Errorf("rewrite requires at least one operation (--replace/--delete/--insert-before/--insert-after)")
	}

	multi := fs.NArg() > 1
	changedFiles, totalEdits := 0, 0

	for _, path := range fs.Args() {
		src, err := loadSource(path, langName, stdinReader())
		if err != nil {
			return err
		}
		matches, err := engine.Query(context.Background(), src.data, src.sitter(), query)
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}
		edits, err := buildEdits(matches, ops)
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}
		out, err := engine.Apply(src.data, edits)
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}

		changed := !bytesEqual(out, src.data)
		if changed {
			changedFiles++
			totalEdits += len(edits)
		}

		switch {
		case diff:
			if changed {
				fmt.Fprint(stdout, unifiedDiff(path, src.data, out))
			}
		case write:
			if path == "-" {
				return fmt.Errorf("cannot use -w when reading from stdin")
			}
			if changed {
				info, statErr := os.Stat(path)
				mode := os.FileMode(0o644)
				if statErr == nil {
					mode = info.Mode()
				}
				if err := os.WriteFile(path, out, mode); err != nil {
					return err
				}
				fmt.Fprintf(stderr, "rewrote %s (%d edit(s))\n", path, len(edits))
			}
		default:
			if multi {
				fmt.Fprintf(stdout, "==> %s <==\n", path)
			}
			if _, err := stdout.Write(out); err != nil {
				return err
			}
		}
	}

	if write {
		fmt.Fprintf(stderr, "%d edit(s) across %d file(s)\n", totalEdits, changedFiles)
	}
	return nil
}

// parseOps validates and collects rewrite operations from the raw flag values.
func parseOps(replaces, deletes, insertsBefore, insertsAfter stringSlice) ([]op, error) {
	var ops []op
	add := func(kind opKind, raw string, needsValue bool) error {
		cap, text, hasEq := strings.Cut(raw, "=")
		cap = trimAt(strings.TrimSpace(cap))
		if cap == "" {
			return fmt.Errorf("operation %q is missing a capture name", raw)
		}
		if needsValue && !hasEq {
			return fmt.Errorf("operation %q must be of the form @capture=TEXT", raw)
		}
		if !needsValue && hasEq {
			return fmt.Errorf("delete operation %q must not include a value", raw)
		}
		ops = append(ops, op{kind: kind, capture: cap, text: text})
		return nil
	}
	for _, r := range replaces {
		if err := add(opReplace, r, true); err != nil {
			return nil, err
		}
	}
	for _, d := range deletes {
		if err := add(opDelete, d, false); err != nil {
			return nil, err
		}
	}
	for _, r := range insertsBefore {
		if err := add(opInsertBefore, r, true); err != nil {
			return nil, err
		}
	}
	for _, r := range insertsAfter {
		if err := add(opInsertAfter, r, true); err != nil {
			return nil, err
		}
	}
	return ops, nil
}

var interpolatePattern = regexp.MustCompile(`\{\{\s*@?([A-Za-z_][A-Za-z0-9_.]*)\s*\}\}`)

// buildEdits turns matches and operations into byte-range edits. Within a
// replacement, {{name}} is expanded to the text of another capture in the same
// match.
func buildEdits(matches []engine.Match, ops []op) ([]engine.Edit, error) {
	var edits []engine.Edit
	for _, m := range matches {
		for _, o := range ops {
			cap, ok := m.Capture(o.capture)
			if !ok {
				continue
			}
			text, err := interpolate(unescape(o.text), m)
			if err != nil {
				return nil, err
			}
			switch o.kind {
			case opReplace:
				edits = append(edits, engine.Edit{Start: cap.StartByte, End: cap.EndByte, Text: text})
			case opDelete:
				edits = append(edits, engine.Edit{Start: cap.StartByte, End: cap.EndByte, Text: ""})
			case opInsertBefore:
				edits = append(edits, engine.Edit{Start: cap.StartByte, End: cap.StartByte, Text: text})
			case opInsertAfter:
				edits = append(edits, engine.Edit{Start: cap.EndByte, End: cap.EndByte, Text: text})
			}
		}
	}
	return edits, nil
}

func interpolate(text string, m engine.Match) (string, error) {
	var bad string
	out := interpolatePattern.ReplaceAllStringFunc(text, func(match string) string {
		name := interpolatePattern.FindStringSubmatch(match)[1]
		c, ok := m.Capture(name)
		if !ok {
			if bad == "" {
				bad = name
			}
			return match
		}
		return c.Text
	})
	if bad != "" {
		return "", fmt.Errorf("template references unknown capture {{%s}} in this match", bad)
	}
	return out, nil
}

// unescape interprets the common backslash escapes \n, \t, \r, and \\ in
// replacement text so newlines and tabs can be expressed on the command line.
// Unknown escape sequences are left untouched.
func unescape(s string) string {
	if !strings.Contains(s, `\`) {
		return s
	}
	var b strings.Builder
	b.Grow(len(s))
	for i := 0; i < len(s); i++ {
		if s[i] == '\\' && i+1 < len(s) {
			switch s[i+1] {
			case 'n':
				b.WriteByte('\n')
				i++
				continue
			case 't':
				b.WriteByte('\t')
				i++
				continue
			case 'r':
				b.WriteByte('\r')
				i++
				continue
			case '\\':
				b.WriteByte('\\')
				i++
				continue
			}
		}
		b.WriteByte(s[i])
	}
	return b.String()
}

func bytesEqual(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

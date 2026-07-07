package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"

	"github.com/imjasonh/playground/ast/internal/engine"
	"github.com/imjasonh/playground/ast/internal/nav"
)

func cmdRename(args []string, stdout, stderr io.Writer) error {
	fs := flag.NewFlagSet("rename", flag.ContinueOnError)
	fs.SetOutput(stdout)
	var (
		langName  string
		to        string
		at        string
		name      string
		write     bool
		diff      bool
		patchFile string
	)
	fs.StringVar(&langName, "l", "", "language name (default: infer from extension)")
	fs.StringVar(&langName, "lang", "", "language name (default: infer from extension)")
	fs.StringVar(&to, "to", "", "the new name (required)")
	fs.StringVar(&at, "at", "", "target the identifier at LINE:COL (1-based)")
	fs.StringVar(&name, "name", "", "target every local binding with this name")
	fs.BoolVar(&write, "w", false, "write changes back to the file")
	fs.BoolVar(&write, "write", false, "write changes back to the file")
	fs.BoolVar(&diff, "diff", false, "print a unified diff without applying it")
	fs.StringVar(&patchFile, "patch", "", "write a unified diff to this file without applying it")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if to == "" {
		return fmt.Errorf("rename requires --to NEW")
	}
	if (at == "") == (name == "") {
		return fmt.Errorf("rename requires exactly one of --at LINE:COL or --name OLD")
	}
	if write && (diff || patchFile != "") {
		return fmt.Errorf("-w/--write cannot be combined with --diff or --patch")
	}
	if fs.NArg() != 1 {
		return fmt.Errorf("rename takes exactly one file (got %d); locals are resolved within a single file", fs.NArg())
	}

	src, err := loadSource(fs.Arg(0), langName, stdinReader())
	if err != nil {
		return err
	}

	var result *nav.RenameResult
	if at != "" {
		pos, err := parseAt(at)
		if err != nil {
			return err
		}
		result, err = nav.RenameAt(context.Background(), src.data, src.lang, pos)
		if err != nil {
			return fmt.Errorf("%s: %w", src.path, err)
		}
	} else {
		result, err = nav.RenameName(context.Background(), src.data, src.lang, name)
		if err != nil {
			return fmt.Errorf("%s: %w", src.path, err)
		}
	}

	edits := make([]engine.Edit, 0, len(result.Occurrences))
	for _, occ := range result.Occurrences {
		edits = append(edits, engine.Edit{Start: occ.StartByte, End: occ.EndByte, Text: to})
	}
	out, err := engine.Apply(src.data, edits)
	if err != nil {
		return err
	}

	switch {
	case diff || patchFile != "":
		d := unifiedDiff(src.path, src.data, out)
		if diff {
			fmt.Fprint(stdout, d)
		}
		if patchFile != "" {
			if err := os.WriteFile(patchFile, []byte(d), 0o644); err != nil {
				return err
			}
			fmt.Fprintf(stderr, "wrote patch %s (%d occurrence(s) of %q -> %q)\n", patchFile, len(edits), result.Name, to)
		}
	case write:
		if src.path == "-" {
			return fmt.Errorf("cannot use -w when reading from stdin")
		}
		info, statErr := os.Stat(src.path)
		mode := os.FileMode(0o644)
		if statErr == nil {
			mode = info.Mode()
		}
		if err := os.WriteFile(src.path, out, mode); err != nil {
			return err
		}
		fmt.Fprintf(stderr, "renamed %q -> %q at %d occurrence(s) in %s\n", result.Name, to, len(edits), src.path)
	default:
		if _, err := stdout.Write(out); err != nil {
			return err
		}
	}
	return nil
}

// parseAt parses a 1-based "LINE:COL" position into a 0-based nav.Pos.
func parseAt(s string) (nav.Pos, error) {
	l, c, ok := strings.Cut(s, ":")
	if !ok {
		return nav.Pos{}, fmt.Errorf("--at must be LINE:COL (got %q)", s)
	}
	line, err := strconv.Atoi(strings.TrimSpace(l))
	if err != nil || line < 1 {
		return nav.Pos{}, fmt.Errorf("--at line must be a positive integer (got %q)", l)
	}
	col, err := strconv.Atoi(strings.TrimSpace(c))
	if err != nil || col < 1 {
		return nav.Pos{}, fmt.Errorf("--at column must be a positive integer (got %q)", c)
	}
	return nav.Pos{Row: uint32(line - 1), Column: uint32(col - 1)}, nil
}

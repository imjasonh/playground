package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"

	"github.com/imjasonh/playground/ast/internal/engine"
	"github.com/imjasonh/playground/ast/internal/nav"
)

func cmdQuery(args []string, stdout io.Writer) error {
	fs := flag.NewFlagSet("query", flag.ContinueOnError)
	fs.SetOutput(stdout)
	var (
		langName string
		query    string
		capture  string
		kinds    stringSlice
	)
	fs.StringVar(&langName, "l", "", "language name (default: infer from extension)")
	fs.StringVar(&langName, "lang", "", "language name (default: infer from extension)")
	fs.StringVar(&query, "q", "", "tree-sitter query selector")
	fs.StringVar(&query, "query", "", "tree-sitter query selector")
	fs.Var(&kinds, "kind", "select nodes by normalized kind, e.g. function (repeatable; see `ast kinds`)")
	fs.StringVar(&capture, "c", "", "only show this capture name")
	fs.StringVar(&capture, "capture", "", "only show this capture name")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if query == "" && len(kinds) == 0 {
		return fmt.Errorf("query requires -q/--query or --kind")
	}
	if query != "" && len(kinds) > 0 {
		return fmt.Errorf("-q/--query and --kind are mutually exclusive")
	}
	if fs.NArg() == 0 {
		return fmt.Errorf("query requires at least one file (or - for stdin)")
	}

	type fileResult struct {
		File    string         `json:"file"`
		Matches []engine.Match `json:"matches"`
	}
	var results []fileResult
	total := 0

	for _, path := range fs.Args() {
		src, err := loadSource(path, langName, stdinReader())
		if err != nil {
			return err
		}
		var matches []engine.Match
		if len(kinds) > 0 {
			matches, err = kindMatches(context.Background(), src, kinds)
		} else {
			matches, err = engine.Query(context.Background(), src.data, src.sitter(), query)
		}
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}
		matches = filterCaptures(matches, capture)
		results = append(results, fileResult{File: path, Matches: matches})
		for _, m := range matches {
			total += len(m.Captures)
		}
	}

	if *asJSON {
		enc := json.NewEncoder(stdout)
		enc.SetIndent("", "  ")
		return enc.Encode(results)
	}

	for _, r := range results {
		for _, m := range r.Matches {
			for _, c := range m.Captures {
				fmt.Fprintf(stdout, "%s:%d:%d: @%s (%s) %s\n",
					r.File, c.Start.Row+1, c.Start.Column+1, c.Name, c.Type, oneLine(c.Text))
			}
		}
	}
	fmt.Fprintf(stdout, "\n%d node(s) matched\n", total)
	return nil
}

// kindMatches runs the normalized --kind selector and adapts the results to
// the engine.Match shape used by the printer, using the kind as the capture
// name (so output reads like "@function").
func kindMatches(ctx context.Context, src *source, kinds []string) ([]engine.Match, error) {
	hits, err := nav.SelectKinds(ctx, src.data, src.lang, kinds)
	if err != nil {
		return nil, err
	}
	matches := make([]engine.Match, 0, len(hits))
	for _, h := range hits {
		c := h.Capture
		c.Name = h.Kind
		matches = append(matches, engine.Match{Captures: []engine.Capture{c}})
	}
	return matches, nil
}

// filterCaptures optionally restricts each match to a single capture name.
func filterCaptures(matches []engine.Match, name string) []engine.Match {
	if name == "" {
		return matches
	}
	name = trimAt(name)
	var out []engine.Match
	for _, m := range matches {
		var kept []engine.Capture
		for _, c := range m.Captures {
			if c.Name == name {
				kept = append(kept, c)
			}
		}
		if len(kept) > 0 {
			out = append(out, engine.Match{PatternIndex: m.PatternIndex, Captures: kept})
		}
	}
	return out
}

func trimAt(s string) string {
	if len(s) > 0 && s[0] == '@' {
		return s[1:]
	}
	return s
}

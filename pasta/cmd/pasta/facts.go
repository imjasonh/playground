package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"sort"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/codefacts"
)

// runFacts is the `pasta facts <tool> [path...]` command: the same AST
// cleanup-fact tools the MCP server exposes, from the shell. Output is JSON.
//
//	pasta facts report ./...
//	pasta facts constant_arguments --min-calls 4 --literals-only pkg/
//	pasta facts symbol_info --name Close
//	pasta facts find_nodes --lang go --node-type if_statement
func runFacts(args []string) int {
	fs := flag.NewFlagSet("pasta facts", flag.ExitOnError)
	langs := fs.String("lang", "", "comma-separated languages to include (default: all supported)")
	exclude := fs.String("exclude", "", "comma-separated slash-path globs to drop (e.g. 'litestream/**,**/*.gen.go')")
	noTests := fs.Bool("no-tests", false, "skip test-convention files entirely")
	noGen := fs.Bool("no-generated", false, "skip generated files entirely")
	minCalls := fs.Int("min-calls", 2, "constant_arguments: minimum call sites")
	literalsOnly := fs.Bool("literals-only", false, "constant_arguments: only literal values")
	minConf := fs.String("min-confidence", "", "unused_symbols: high|medium|low")
	name := fs.String("name", "", "symbol name for references/impact/symbol_info/argument_values/call_sites")
	index := fs.Int("index", 0, "argument_values: zero-based argument position")
	by := fs.String("by", "", "hotspots: branches|lines|params|fan_in|depth")
	limit := fs.Int("limit", 0, "row/match limit where applicable")
	minSize := fs.Int("min-size", 0, "duplicate_bodies: minimum body node count")
	defLang := fs.String("def-lang", "", "definitions: filter by language")
	nodeType := fs.String("node-type", "", "find_nodes: tree-sitter node type")
	textRe := fs.String("text-regex", "", "find_nodes: RE2 regexp the node text must match")

	if len(args) == 0 {
		listFactsTools()
		return 2
	}
	tool, ok := codefacts.ToolByName(args[0])
	if !ok {
		fmt.Fprintf(os.Stderr, "unknown facts tool %q\n", args[0])
		listFactsTools()
		return 2
	}
	if err := fs.Parse(args[1:]); err != nil {
		return 2
	}
	roots := fs.Args()
	if len(roots) == 0 {
		roots = []string{"."}
	}

	a := map[string]any{
		"min_calls": float64(*minCalls), "literals_only": *literalsOnly,
		"min_confidence": *minConf, "name": *name, "index": float64(*index),
		"by": *by, "min_size": float64(*minSize), "lang": *defLang,
		"node_type": *nodeType, "text_regex": *textRe,
	}
	if *limit > 0 {
		a["limit"] = float64(*limit)
	}

	ctx := context.Background()
	var result any
	var err error
	if tool.NeedsRoots != nil {
		result, err = tool.NeedsRoots(ctx, roots, a)
	} else {
		opts := codefacts.DefaultBuildOptions()
		opts.IncludeTests = !*noTests
		opts.IncludeGen = !*noGen
		if *langs != "" {
			opts.Langs = splitComma(*langs)
		}
		if *exclude != "" {
			opts.Exclude = splitComma(*exclude)
		}
		var idx *codefacts.Index
		idx, err = codefacts.Build(ctx, roots, opts)
		if err == nil {
			result, err = tool.Indexed(idx, a)
		}
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	if err := enc.Encode(result); err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	return 0
}

func listFactsTools() {
	fmt.Fprintln(os.Stderr, "usage: pasta facts <tool> [flags] [path...]\n\ntools:")
	tools := codefacts.Tools()
	sort.Slice(tools, func(i, j int) bool { return tools[i].Name < tools[j].Name })
	for _, t := range tools {
		fmt.Fprintf(os.Stderr, "  %-22s %s\n", t.Name, t.Description)
	}
}

func splitComma(s string) []string {
	var out []string
	for _, p := range strings.Split(s, ",") {
		if p = strings.TrimSpace(p); p != "" {
			out = append(out, p)
		}
	}
	return out
}

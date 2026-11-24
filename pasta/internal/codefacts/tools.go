package codefacts

import (
	"context"
	"fmt"
)

// Tool is one agent-facing operation over an indexed source tree.
type Tool struct {
	Name        string
	Description string
	// Params documents extra arguments beyond the shared path/langs/exclude set,
	// as JSON-schema property objects keyed by name.
	Params map[string]any
	// Indexed handlers answer from a prebuilt index. NeedsRoots handlers (only
	// find_nodes today) walk the tree themselves.
	Indexed    func(idx *Index, args map[string]any) (any, error)
	NeedsRoots func(ctx context.Context, roots []string, args map[string]any) (any, error)
}

func strProp(desc string) map[string]any {
	return map[string]any{"type": "string", "description": desc}
}
func intProp(desc string) map[string]any {
	return map[string]any{"type": "integer", "description": desc}
}
func boolProp(desc string) map[string]any {
	return map[string]any{"type": "boolean", "description": desc}
}

func argStr(args map[string]any, key string) string {
	if v, ok := args[key].(string); ok {
		return v
	}
	return ""
}
func argInt(args map[string]any, key string, def int) int {
	switch v := args[key].(type) {
	case float64:
		return int(v)
	case int:
		return v
	}
	return def
}
func argBool(args map[string]any, key string) bool {
	b, _ := args[key].(bool)
	return b
}
func argExported(args map[string]any) *bool {
	if v, ok := args["exported"].(bool); ok {
		return &v
	}
	return nil
}

// Tools returns the registry in a stable order.
func Tools() []Tool {
	return []Tool{
		{
			Name:        "report",
			Description: "One-shot cleanup summary across every sweep, plus coverage and the top high-confidence unused symbols (with a production-only count).",
			Indexed:     func(idx *Index, _ map[string]any) (any, error) { return Report(idx), nil },
		},
		{
			Name:        "coverage",
			Description: "What parsed, per language: files, definitions, calls, and the supported-language list.",
			Indexed:     func(idx *Index, _ map[string]any) (any, error) { return Coverage(idx), nil },
		},
		{
			Name:        "constant_arguments",
			Description: "Parameters every call passes the same value (a removable argument). Literals rank first; bare identifiers (naming conventions) sink.",
			Params: map[string]any{
				"min_calls":     intProp("minimum call sites supplying the argument (default 2)"),
				"literals_only": boolProp("only report literal constant values"),
			},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				cands := ConstantArguments(idx, argInt(a, "min_calls", 2))
				if argBool(a, "literals_only") {
					var f []Candidate
					for _, c := range cands {
						if c.ValueKind == "literal" {
							f = append(f, c)
						}
					}
					cands = f
				}
				return map[string]any{"count": len(cands), "candidates": cands}, nil
			},
		},
		{
			Name:        "unused_symbols",
			Description: "Definitions nothing references by name. Ranks production, high-confidence first; methods and interface/test/entrypoint symbols are excluded or down-ranked.",
			Params:      map[string]any{"min_confidence": strProp("high|medium|low (default low)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				u := UnusedSymbols(idx, true)
				if mc := argStr(a, "min_confidence"); mc != "" {
					limit := confRank(mc)
					var f []Unused
					for _, x := range u {
						if confRank(x.Confidence) <= limit {
							f = append(f, x)
						}
					}
					u = f
				}
				return map[string]any{"count": len(u), "unused": u}, nil
			},
		},
		{
			Name:        "dead_code",
			Description: "Transitively unreachable definitions via the call graph (DCE-lite). Roots include exports, entrypoints, tests, value-refs, string-refs, and dynamically dispatched methods.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				d := DeadCode(idx)
				return map[string]any{"count": len(d), "dead_code": d}, nil
			},
		},
		{
			Name:        "unused_parameters",
			Description: "Parameters never read in the body. Skips underscore-prefixed and self/this/cls params, and interface/trait method params (signature is pinned).",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				p := UnusedParameters(idx)
				return map[string]any{"count": len(p), "unused_parameters": p}, nil
			},
		},
		{
			Name:        "unreachable_code",
			Description: "Statements after a terminator (return/break/continue/throw) in the same block.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := UnreachableCode(idx)
				return map[string]any{"count": len(r), "unreachable": r}, nil
			},
		},
		{
			Name:        "unused_imports",
			Description: "Imports whose bound name never appears as an identifier in the file (Go, Python).",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := UnusedImports(idx)
				return map[string]any{"count": len(r), "unused_imports": r}, nil
			},
		},
		{
			Name:        "constant_returns",
			Description: "Functions whose every return yields the same literal. Interface/trait methods are excluded (signature is pinned). Call counts are per-definition where the name is unique.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := ConstantReturns(idx)
				return map[string]any{"count": len(r), "constant_returns": r}, nil
			},
		},
		{
			Name:        "redundant_conditions",
			Description: "Comparisons to a boolean literal (x == true). Strict equality in JS/TS is flagged low-confidence because it is only redundant on a boolean-typed operand.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := RedundantConditions(idx)
				return map[string]any{"count": len(r), "redundant": r}, nil
			},
		},
		{
			Name:        "constant_conditions",
			Description: "Branches with a literal condition (if true / if false): dead or always-run code.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := ConstantConditions(idx)
				return map[string]any{"count": len(r), "constant_conditions": r}, nil
			},
		},
		{
			Name:        "unexport_candidates",
			Description: "Exported definitions whose every in-tree caller shares the package. Name-based (no symbol resolution), so judge before unexporting a public API.",
			Indexed: func(idx *Index, _ map[string]any) (any, error) {
				r := UnexportCandidates(idx)
				return map[string]any{"count": len(r), "unexport": r}, nil
			},
		},
		{
			Name:        "duplicate_bodies",
			Description: "Functions with identical body structure (structural hash), a refactor-to-shared-helper signal. Production groups rank above all-test groups.",
			Params:      map[string]any{"min_size": intProp("minimum body node count (default 40)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				r := DuplicateBodies(idx, argInt(a, "min_size", 40))
				return map[string]any{"count": len(r), "duplicates": r}, nil
			},
		},
		{
			Name:        "definitions",
			Description: "List definitions with metrics (params, call count, lines, branches).",
			Params:      map[string]any{"lang": strProp("filter by language"), "exported": boolProp("filter by export status")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				r := Definitions(idx, argStr(a, "lang"), argExported(a))
				return map[string]any{"count": len(r), "definitions": r}, nil
			},
		},
		{
			Name:        "hotspots",
			Description: "Definitions ranked by complexity/size/fan-in. fan_in is per-definition when the name is unique, else same-directory calls.",
			Params:      map[string]any{"by": strProp("branches|lines|params|fan_in|depth (default branches)"), "limit": intProp("max rows (default 25)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				r := Hotspots(idx, argStr(a, "by"), argInt(a, "limit", 25))
				return map[string]any{"hotspots": r}, nil
			},
		},
		{
			Name:        "references",
			Description: "Occurrences, definitions, calls, and value-refs for a name.",
			Params:      map[string]any{"name": strProp("symbol name (required)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				if argStr(a, "name") == "" {
					return nil, fmt.Errorf("name is required")
				}
				return References(idx, argStr(a, "name")), nil
			},
		},
		{
			Name:        "impact",
			Description: "Transitive callers of a name (who breaks if it changes), in layers.",
			Params:      map[string]any{"name": strProp("symbol name (required)"), "max_depth": intProp("caller depth (default 6)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				if argStr(a, "name") == "" {
					return nil, fmt.Errorf("name is required")
				}
				return Impact(idx, argStr(a, "name"), argInt(a, "max_depth", 6)), nil
			},
		},
		{
			Name:        "argument_values",
			Description: "Value distribution for one parameter position across all call sites of a name.",
			Params:      map[string]any{"name": strProp("symbol name (required)"), "index": intProp("zero-based argument position (required)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				if argStr(a, "name") == "" {
					return nil, fmt.Errorf("name is required")
				}
				return ArgumentValues(idx, argStr(a, "name"), argInt(a, "index", 0)), nil
			},
		},
		{
			Name:        "call_sites",
			Description: "Locations that call a name, with qualifier and arguments.",
			Params:      map[string]any{"name": strProp("symbol name (required)"), "limit": intProp("max rows (default 50)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				if argStr(a, "name") == "" {
					return nil, fmt.Errorf("name is required")
				}
				r := CallSites(idx, argStr(a, "name"), argInt(a, "limit", 50))
				return map[string]any{"count": len(r), "call_sites": r}, nil
			},
		},
		{
			Name:        "symbol_info",
			Description: "A name's definitions, export status, collisions, call count, and value-use estimate — the facts to judge a finding.",
			Params:      map[string]any{"name": strProp("symbol name (required)")},
			Indexed: func(idx *Index, a map[string]any) (any, error) {
				if argStr(a, "name") == "" {
					return nil, fmt.Errorf("name is required")
				}
				return SymbolInfo(idx, argStr(a, "name")), nil
			},
		},
		{
			Name:        "find_nodes",
			Description: "Generic escape hatch: find AST nodes by tree-sitter node type, optionally filtered by a Go regexp on the node's text. Returns path/line/text.",
			Params: map[string]any{
				"lang":       strProp("language name (required)"),
				"node_type":  strProp("tree-sitter node type, e.g. if_statement (required)"),
				"text_regex": strProp("optional RE2 regexp the node text must match"),
				"limit":      intProp("max matches (default 200)"),
			},
			NeedsRoots: func(ctx context.Context, roots []string, a map[string]any) (any, error) {
				if argStr(a, "lang") == "" || argStr(a, "node_type") == "" {
					return nil, fmt.Errorf("lang and node_type are required")
				}
				return FindNodes(ctx, roots, argStr(a, "lang"), argStr(a, "node_type"), argStr(a, "text_regex"), argInt(a, "limit", 200))
			},
		},
	}
}

// ToolByName returns the named tool, or ok=false.
func ToolByName(name string) (Tool, bool) {
	for _, t := range Tools() {
		if t.Name == name {
			return t, true
		}
	}
	return Tool{}, false
}

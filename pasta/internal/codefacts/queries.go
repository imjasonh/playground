package codefacts

import (
	"context"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/tsutil"
	"github.com/imjasonh/playground/pasta/internal/tswasm"
)

func Definitions(idx *Index, lang string, exported *bool) []map[string]any {
	var out []map[string]any
	for _, defs := range idx.defs {
		for _, d := range defs {
			if lang != "" && d.Lang != lang {
				continue
			}
			if exported != nil && (d.Exported == nil || *d.Exported != *exported) {
				continue
			}
			cc, amb := callCountFor(idx, d)
			m := map[string]any{
				"name": d.Name, "qualified": d.Qualified(), "path": d.Path, "line": d.Line,
				"end_line": d.EndLine, "params": d.Params, "exported": d.Exported, "lang": d.Lang,
				"call_count": cc, "lines": d.Lines, "branches": d.Branches, "is_test": d.IsTest,
			}
			if amb {
				m["call_count_ambiguous"] = true
			}
			out = append(out, m)
		}
	}
	sort.Slice(out, func(a, b int) bool {
		pa, pb := out[a]["path"].(string), out[b]["path"].(string)
		if pa != pb {
			return pa < pb
		}
		return out[a]["line"].(int) < out[b]["line"].(int)
	})
	return out
}

func References(idx *Index, name string) map[string]any {
	sites := idx.identSites[name]
	ss := make([]map[string]any, 0, len(sites))
	for _, s := range sites {
		ss = append(ss, map[string]any{"path": s.path, "line": s.line})
	}
	return map[string]any{
		"name": name, "total_occurrences": idx.identUses[name],
		"definitions": len(idx.defs[name]), "calls": len(idx.calls[name]),
		"value_refs": valueRefs(idx, name), "truncated": len(sites) >= identSiteCap,
		"sites": ss,
	}
}

func Impact(idx *Index, name string, maxDepth int) map[string]any {
	if maxDepth <= 0 {
		maxDepth = 6
	}
	reverse := map[string]map[string]bool{}
	for cid, callees := range idx.callEdges {
		caller := idx.defsByID[cid].Name
		for callee := range callees {
			if reverse[callee] == nil {
				reverse[callee] = map[string]bool{}
			}
			reverse[callee][caller] = true
		}
	}
	seen := map[string]bool{}
	var layers [][]string
	frontier := map[string]bool{name: true}
	for depth := 0; len(frontier) > 0 && depth < maxDepth; depth++ {
		next := map[string]bool{}
		for nm := range frontier {
			for caller := range reverse[nm] {
				if !seen[caller] && caller != name {
					seen[caller] = true
					next[caller] = true
				}
			}
		}
		if len(next) > 0 {
			layers = append(layers, sortedKeys(next))
		}
		frontier = next
	}
	return map[string]any{
		"name": name, "direct_callers": sortedKeys(reverse[name]),
		"transitive_caller_count": len(seen), "layers": layers,
	}
}

func sortedKeys(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func Hotspots(idx *Index, by string, limit int) []map[string]any {
	if limit <= 0 {
		limit = 25
	}
	var rows []*Def
	for _, defs := range idx.defs {
		rows = append(rows, defs...)
	}
	keyFn := func(d *Def) int {
		switch by {
		case "lines":
			return d.Lines
		case "params":
			return len(d.Params)
		case "fan_in":
			c, _ := callCountFor(idx, d)
			return c
		case "depth":
			return d.Depth
		default:
			return d.Branches
		}
	}
	sort.Slice(rows, func(a, b int) bool { return keyFn(rows[a]) > keyFn(rows[b]) })
	if len(rows) > limit {
		rows = rows[:limit]
	}
	out := make([]map[string]any, 0, len(rows))
	for _, d := range rows {
		fanIn, amb := callCountFor(idx, d)
		m := map[string]any{
			"name": d.Name, "qualified": d.Qualified(), "path": d.Path, "line": d.Line,
			"lang": d.Lang, "branches": d.Branches, "lines": d.Lines, "params": len(d.Params),
			"depth": d.Depth, "fan_in": fanIn, "is_test": d.IsTest,
		}
		if amb {
			m["fan_in_ambiguous"] = true
		}
		out = append(out, m)
	}
	return out
}

func Coverage(idx *Index) map[string]any {
	defsByLang := map[string]int{}
	for _, defs := range idx.defs {
		for _, d := range defs {
			defsByLang[d.Lang]++
		}
	}
	callsByLang := map[string]int{}
	for _, calls := range idx.calls {
		for _, c := range calls {
			callsByLang[c.Lang]++
		}
	}
	langs := sortedKeys(idx.langs)
	per := map[string]any{}
	for _, l := range langs {
		per[l] = map[string]any{
			"files": idx.filesByLang[l], "definitions": defsByLang[l], "calls": callsByLang[l],
		}
	}
	return map[string]any{
		"files": idx.files, "languages": langs, "per_language": per,
		"supported_languages": SupportedLanguages(),
	}
}

func Report(idx *Index) map[string]any {
	unused := UnusedSymbols(idx, true)
	var high []map[string]any
	prodHigh := 0
	for _, u := range unused {
		if u.Confidence == "high" {
			if !u.IsTest && !u.IsGenerated {
				prodHigh++
			}
			if len(high) < 25 {
				high = append(high, map[string]any{"name": u.Name, "qualified": u.Qualified, "path": u.Path, "line": u.Line, "is_test": u.IsTest})
			}
		}
	}
	return map[string]any{
		"coverage": Coverage(idx),
		"counts": map[string]any{
			"unused_symbols":        len(unused),
			"dead_code_transitive":  len(DeadCode(idx)),
			"unused_parameters":     len(UnusedParameters(idx)),
			"unreachable_code":      len(UnreachableCode(idx)),
			"unused_imports":        len(UnusedImports(idx)),
			"constant_arguments":    len(ConstantArguments(idx, 2)),
			"constant_conditions":   len(ConstantConditions(idx)),
			"redundant_conditions":  len(RedundantConditions(idx)),
			"constant_returns":      len(ConstantReturns(idx)),
			"unexport_candidates":   len(UnexportCandidates(idx)),
			"duplicate_body_groups": len(DuplicateBodies(idx, 40)),
		},
		"high_confidence_unused":            high,
		"high_confidence_unused_production": prodHigh,
	}
}

func ArgumentValues(idx *Index, name string, index int) map[string]any {
	calls := idx.calls[name]
	dist := map[string]int{}
	kinds := map[string]string{}
	for _, c := range calls {
		if len(c.Args) > index {
			v := c.Args[index]
			dist[v]++
			if index < len(c.Kinds) {
				kinds[v] = c.Kinds[index]
			}
		}
	}
	type kv struct {
		v string
		n int
	}
	var pairs []kv
	supplying := 0
	for v, n := range dist {
		pairs = append(pairs, kv{v, n})
		supplying += n
	}
	sort.Slice(pairs, func(a, b int) bool { return pairs[a].n > pairs[b].n })
	var distribution []map[string]any
	for _, p := range pairs {
		k := kinds[p.v]
		if k == "" {
			k = "expr"
		}
		distribution = append(distribution, map[string]any{"value": p.v, "count": p.n, "kind": k})
	}
	return map[string]any{
		"name": name, "index": index, "call_count": len(calls),
		"supplying_count": supplying, "distinct": len(dist), "distribution": distribution,
	}
}

func CallSites(idx *Index, name string, limit int) []map[string]any {
	if limit <= 0 {
		limit = 50
	}
	calls := idx.calls[name]
	if len(calls) > limit {
		calls = calls[:limit]
	}
	out := make([]map[string]any, 0, len(calls))
	for _, c := range calls {
		out = append(out, map[string]any{
			"path": c.Path, "line": c.Line, "qualifier": c.Qualifier, "form": c.Form, "args": c.Args,
		})
	}
	return out
}

func SymbolInfo(idx *Index, name string) map[string]any {
	defs := idx.defs[name]
	calls := idx.calls[name]
	quals := map[string]bool{}
	for _, c := range calls {
		if c.Qualifier != "" {
			quals[c.Qualifier] = true
		}
	}
	qs := sortedKeys(quals)
	if len(qs) > 20 {
		qs = qs[:20]
	}
	var exported *bool
	if len(defs) > 0 {
		exported = defs[0].Exported
	}
	var defList []map[string]any
	for i, d := range defs {
		if i >= 20 {
			break
		}
		defList = append(defList, map[string]any{
			"path": d.Path, "line": d.Line, "end_line": d.EndLine, "qualified": d.Qualified(),
			"params": d.Params, "exported": d.Exported, "lang": d.Lang, "lines": d.Lines,
			"branches": d.Branches, "unused_params": d.UnusedP, "const_return": d.ConstReturn,
			"is_method": d.IsMethod, "is_interface_method": isInterfaceMethod(idx, d), "is_test": d.IsTest,
		})
	}
	return map[string]any{
		"name": name, "has_def": len(defs) > 0, "def_count": len(defs), "exported": exported,
		"call_count": len(calls), "distinct_qualifiers": qs,
		"value_used_estimate": valueRefs(idx, name), "definitions": defList,
	}
}

// FindNodes is the generic escape hatch: find nodes by type (optionally filtered
// by a regexp on their text), returning path/line/text. It replaces the Python
// prototype's raw tree-sitter query, which needs a query runtime the wazero
// backend does not expose. Useful to target a shape the built-in sweeps do not
// name.
func FindNodes(ctx context.Context, roots []string, langName, nodeType, textRe string, limit int) (map[string]any, error) {
	if limit <= 0 {
		limit = 200
	}
	spec := specs[langName]
	if spec == nil {
		return map[string]any{"error": "unknown language: " + langName, "matches": []any{}}, nil
	}
	var re *regexp.Regexp
	if textRe != "" {
		r, err := regexp.Compile(textRe)
		if err != nil {
			return map[string]any{"error": "invalid regexp: " + err.Error(), "matches": []any{}}, nil
		}
		re = r
	}
	lang := &tswasm.Language{Grammar: spec.grammar}
	var matches []map[string]any
	truncated := false
	for _, root := range roots {
		if truncated {
			break
		}
		_ = filepath.WalkDir(root, func(p string, d os.DirEntry, err error) error {
			if err != nil || truncated {
				return nil
			}
			if d.IsDir() {
				if p != root && skipDirs[d.Name()] {
					return filepath.SkipDir
				}
				return nil
			}
			if extToLang[strings.ToLower(filepath.Ext(p))] != langName {
				return nil
			}
			fi, e := d.Info()
			if e != nil || fi.Size() > (2<<20) {
				return nil
			}
			src, e := os.ReadFile(p)
			if e != nil {
				return nil
			}
			tree, rootNode, e := tsutil.Parse(ctx, lang, src, p)
			if e != nil || !rootNode.IsValid() {
				return nil
			}
			defer tree.Release()
			lm := newLineMap(src)
			rel := relOf(p, root)
			tsutil.Walk(rootNode, func(n tsutil.Node) bool {
				if truncated {
					return false
				}
				if n.Type() == nodeType {
					txt := norm(n.Text())
					if re == nil || re.MatchString(txt) {
						matches = append(matches, map[string]any{
							"path": rel, "line": lm.line(n.StartByte()), "text": trunc(txt, 200),
						})
						if len(matches) >= limit {
							truncated = true
							return false
						}
					}
				}
				return true
			})
			return nil
		})
	}
	return map[string]any{"count": len(matches), "truncated": truncated, "matches": matches}, nil
}

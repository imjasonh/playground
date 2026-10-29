package codefacts

import (
	"path/filepath"
	"sort"
)

// confRank orders confidence tiers; lower is stronger.
func confRank(c string) int {
	switch c {
	case "high":
		return 0
	case "medium":
		return 1
	default:
		return 2
	}
}

// scopeRank floats production code above test and generated code.
func scopeRank(isTest, isGen bool) int {
	r := 0
	if isTest {
		r++
	}
	if isGen {
		r += 2
	}
	return r
}

// isInterfaceMethod reports whether d's signature is pinned by an interface or
// trait (declared in-tree, or a well-known Go stdlib interface), so const-return
// / unused-param / unused findings on it are unreliable.
func isInterfaceMethod(idx *Index, d *Def) bool {
	if !d.IsMethod {
		return false
	}
	if idx.ifaceMethods[d.Name] {
		return true
	}
	return d.Lang == "go" && goStdlibIfaceMethods[d.Name]
}

// callCountFor returns this definition's call count. When the name is unique the
// name-global count is exact; when several defs share the name it is ambiguous,
// so it returns same-directory calls as a local proxy and reports ambiguous=true.
func callCountFor(idx *Index, d *Def) (count int, ambiguous bool) {
	all := len(idx.calls[d.Name])
	if len(idx.defs[d.Name]) <= 1 {
		return all, false
	}
	return sameDirCalls(idx, d.Name, d.Dir), true
}

// Candidate is a constant-argument finding.
type Candidate struct {
	Name          string `json:"name"`
	Index         int    `json:"index"`
	Param         string `json:"param,omitempty"`
	Value         string `json:"value"`
	ValueKind     string `json:"value_kind"`
	CallCount     int    `json:"call_count"`
	DistinctQuals int    `json:"distinct_qualifiers"`
	Exported      *bool  `json:"exported"`
	DefCount      int    `json:"def_count"`
	HasDef        bool   `json:"has_def"`
	ValueUsed     int    `json:"value_used"`
	Confidence    string `json:"confidence"`
	IsTest        bool   `json:"is_test"`
}

func ConstantArguments(idx *Index, minCalls int) []Candidate {
	if minCalls < 2 {
		minCalls = 2
	}
	var out []Candidate
	for name, calls := range idx.calls {
		maxArity := 0
		for _, c := range calls {
			if len(c.Args) > maxArity {
				maxArity = len(c.Args)
			}
		}
		defs := idx.defs[name]
		var exported *bool
		isTest := false
		if len(defs) > 0 {
			exported = defs[0].Exported
			isTest = defs[0].IsTest
		}
		vu := valueRefs(idx, name)
		for i := 0; i < maxArity; i++ {
			var supplying []*Call
			for _, c := range calls {
				if len(c.Args) > i {
					supplying = append(supplying, c)
				}
			}
			if len(supplying) < minCalls {
				continue
			}
			values := map[string]bool{}
			for _, c := range supplying {
				values[canonValue(c.Args[i])] = true
			}
			if len(values) != 1 {
				continue
			}
			d0 := supplying[0]
			if suppressedAt(idx, d0.Path, d0.Line) {
				continue
			}
			kinds := map[string]bool{}
			for _, c := range supplying {
				if i < len(c.Kinds) {
					kinds[c.Kinds[i]] = true
				}
			}
			valueKind := "expr"
			if len(kinds) == 1 {
				for k := range kinds {
					valueKind = k
				}
			}
			quals := map[string]bool{}
			for _, c := range supplying {
				if c.Qualifier != "" {
					quals[c.Qualifier] = true
				}
			}
			param := ""
			for _, d := range defs {
				if i < len(d.Params) {
					param = d.Params[i]
					break
				}
			}
			out = append(out, Candidate{
				Name: name, Index: i, Param: param, Value: supplying[0].Args[i],
				ValueKind: valueKind, CallCount: len(supplying), DistinctQuals: len(quals),
				Exported: exported, DefCount: len(defs), HasDef: len(defs) > 0, ValueUsed: vu,
				Confidence: confConst(exported, len(defs), len(defs) > 0, vu, len(supplying)),
				IsTest:     isTest,
			})
		}
	}
	kindRank := map[string]int{"literal": 0, "const": 1, "expr": 2, "ident": 3}
	sort.Slice(out, func(a, b int) bool {
		x, y := out[a], out[b]
		if kindRank[x.ValueKind] != kindRank[y.ValueKind] {
			return kindRank[x.ValueKind] < kindRank[y.ValueKind]
		}
		if sx, sy := scopeRank(x.IsTest, false), scopeRank(y.IsTest, false); sx != sy {
			return sx < sy
		}
		if confRank(x.Confidence) != confRank(y.Confidence) {
			return confRank(x.Confidence) < confRank(y.Confidence)
		}
		return x.CallCount > y.CallCount
	})
	return out
}

func confConst(exported *bool, defCount int, hasDef bool, valueUsed, calls int) string {
	if !hasDef {
		return "low"
	}
	if defCount > 1 || (exported != nil && *exported) || valueUsed > 0 {
		return "medium"
	}
	if calls >= 3 {
		return "high"
	}
	return "medium"
}

// Unused is an unused-symbol finding.
type Unused struct {
	Name        string   `json:"name"`
	Qualified   string   `json:"qualified,omitempty"`
	Path        string   `json:"path"`
	Line        int      `json:"line"`
	EndLine     int      `json:"end_line"`
	Params      []string `json:"params,omitempty"`
	Exported    *bool    `json:"exported"`
	Lang        string   `json:"lang"`
	DefCount    int      `json:"def_count"`
	Confidence  string   `json:"confidence"`
	IsTest      bool     `json:"is_test"`
	IsGenerated bool     `json:"is_generated"`
}

func UnusedSymbols(idx *Index, includeExported bool) []Unused {
	var out []Unused
	for name, defs := range idx.defs {
		if idx.identUses[name]-len(defs) > 0 {
			continue
		}
		if idx.stringRefs[name] {
			continue
		}
		for _, d := range defs {
			if d.RuntimeRoot || isInterfaceMethod(idx, d) {
				continue
			}
			if (d.Exported != nil && *d.Exported && !includeExported) || suppressedAt(idx, d.Path, d.Line) {
				continue
			}
			var conf string
			switch {
			case d.Exported == nil || (d.Exported != nil && *d.Exported):
				conf = "low"
			case d.IsMethod:
				conf = "medium"
			case len(defs) == 1:
				conf = "high"
			default:
				conf = "medium"
			}
			out = append(out, Unused{
				Name: name, Qualified: d.Qualified(), Path: d.Path, Line: d.Line, EndLine: d.EndLine,
				Params: d.Params, Exported: d.Exported, Lang: d.Lang, DefCount: len(defs),
				Confidence: conf, IsTest: d.IsTest, IsGenerated: d.IsGenerated,
			})
		}
	}
	sortFindings(out, func(u Unused) (string, bool, bool, string, int) {
		return u.Confidence, u.IsTest, u.IsGenerated, u.Path, u.Line
	})
	return out
}

// DeadItem is a transitively-unreachable definition.
type DeadItem struct {
	Name        string `json:"name"`
	Qualified   string `json:"qualified,omitempty"`
	Path        string `json:"path"`
	Line        int    `json:"line"`
	EndLine     int    `json:"end_line"`
	Lang        string `json:"lang"`
	Exported    *bool  `json:"exported"`
	DefCount    int    `json:"def_count"`
	Reason      string `json:"reason"`
	IsTest      bool   `json:"is_test"`
	IsGenerated bool   `json:"is_generated"`
}

func DeadCode(idx *Index) []DeadItem {
	reachable := map[string]bool{}
	for n := range idx.toplevelCall {
		reachable[n] = true
	}
	for name, defs := range idx.defs {
		for _, d := range defs {
			// Guardrail parity with UnusedSymbols: exported, runtime roots,
			// value-referenced, string-referenced, AND dynamically dispatched
			// (methods / interface methods) are all roots.
			if (d.Exported != nil && *d.Exported) || d.RuntimeRoot || valueRefs(idx, name) > 0 ||
				idx.stringRefs[name] || d.IsMethod || isInterfaceMethod(idx, d) {
				reachable[name] = true
			}
		}
	}
	frontier := make([]string, 0, len(reachable))
	for n := range reachable {
		frontier = append(frontier, n)
	}
	for len(frontier) > 0 {
		nm := frontier[len(frontier)-1]
		frontier = frontier[:len(frontier)-1]
		for _, d := range idx.defs[nm] {
			for callee := range idx.callEdges[d.ID] {
				if !reachable[callee] {
					reachable[callee] = true
					frontier = append(frontier, callee)
				}
			}
		}
	}
	var out []DeadItem
	for name, defs := range idx.defs {
		if reachable[name] {
			continue
		}
		for _, d := range defs {
			if suppressedAt(idx, d.Path, d.Line) {
				continue
			}
			out = append(out, DeadItem{
				Name: name, Qualified: d.Qualified(), Path: d.Path, Line: d.Line, EndLine: d.EndLine,
				Lang: d.Lang, Exported: d.Exported, DefCount: len(defs),
				Reason: "no path from any root (entrypoint/export/test/value-ref/dispatch)",
				IsTest: d.IsTest, IsGenerated: d.IsGenerated,
			})
		}
	}
	sort.Slice(out, func(a, b int) bool {
		x, y := out[a], out[b]
		if sx, sy := scopeRank(x.IsTest, x.IsGenerated), scopeRank(y.IsTest, y.IsGenerated); sx != sy {
			return sx < sy
		}
		if x.Path != y.Path {
			return x.Path < y.Path
		}
		return x.Line < y.Line
	})
	return out
}

type ParamFinding struct {
	Function  string `json:"function"`
	Qualified string `json:"qualified,omitempty"`
	Param     string `json:"param"`
	Path      string `json:"path"`
	Line      int    `json:"line"`
	Lang      string `json:"lang"`
	Exported  *bool  `json:"exported"`
	IsTest    bool   `json:"is_test"`
}

func UnusedParameters(idx *Index) []ParamFinding {
	var out []ParamFinding
	for name, defs := range idx.defs {
		for _, d := range defs {
			if suppressedAt(idx, d.Path, d.Line) || isInterfaceMethod(idx, d) {
				continue
			}
			for _, p := range d.UnusedP {
				out = append(out, ParamFinding{
					Function: name, Qualified: d.Qualified(), Param: p, Path: d.Path,
					Line: d.Line, Lang: d.Lang, Exported: d.Exported, IsTest: d.IsTest,
				})
			}
		}
	}
	sort.Slice(out, func(a, b int) bool {
		x, y := out[a], out[b]
		if sx, sy := scopeRank(x.IsTest, false), scopeRank(y.IsTest, false); sx != sy {
			return sx < sy
		}
		if x.Path != y.Path {
			return x.Path < y.Path
		}
		return x.Line < y.Line
	})
	return out
}

type SimpleLoc struct {
	Path string `json:"path"`
	Line int    `json:"line"`
	Lang string `json:"lang"`
}

func UnreachableCode(idx *Index) []map[string]any {
	rows := make([]unreach, 0, len(idx.unreachable))
	for _, u := range idx.unreachable {
		if !suppressedAt(idx, u.path, u.line) {
			rows = append(rows, u)
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if rows[a].path != rows[b].path {
			return rows[a].path < rows[b].path
		}
		return rows[a].line < rows[b].line
	})
	out := make([]map[string]any, 0, len(rows))
	for _, u := range rows {
		out = append(out, map[string]any{"path": u.path, "line": u.line, "lang": u.lang, "after": u.after})
	}
	return out
}

func UnusedImports(idx *Index) []map[string]any {
	rows := make([]unusedImport, 0, len(idx.unusedImports))
	for _, u := range idx.unusedImports {
		if !suppressedAt(idx, u.path, u.line) {
			rows = append(rows, u)
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if rows[a].path != rows[b].path {
			return rows[a].path < rows[b].path
		}
		return rows[a].line < rows[b].line
	})
	out := make([]map[string]any, 0, len(rows))
	for _, u := range rows {
		out = append(out, map[string]any{"name": u.name, "path": u.path, "line": u.line, "lang": u.lang, "statement": u.statement})
	}
	return out
}

func ConstantConditions(idx *Index) []map[string]any {
	rows := make([]deadBranch, 0, len(idx.dead))
	for _, d := range idx.dead {
		if !suppressedAt(idx, d.path, d.line) {
			rows = append(rows, d)
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if rows[a].path != rows[b].path {
			return rows[a].path < rows[b].path
		}
		return rows[a].line < rows[b].line
	})
	out := make([]map[string]any, 0, len(rows))
	for _, d := range rows {
		effect := "never runs"
		if d.always {
			effect = "always runs"
		}
		out = append(out, map[string]any{"path": d.path, "line": d.line, "lang": d.lang, "construct": d.construct, "value": d.value, "effect": effect})
	}
	return out
}

func RedundantConditions(idx *Index) []map[string]any {
	rows := make([]redundant, 0, len(idx.redundant))
	for _, r := range idx.redundant {
		if !suppressedAt(idx, r.path, r.line) {
			rows = append(rows, r)
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if rows[a].path != rows[b].path {
			return rows[a].path < rows[b].path
		}
		return rows[a].line < rows[b].line
	})
	out := make([]map[string]any, 0, len(rows))
	for _, r := range rows {
		m := map[string]any{"path": r.path, "line": r.line, "lang": r.lang, "snippet": r.snippet, "kind": r.kind, "operator": r.operator}
		if r.strictInDyn {
			m["note"] = "strict equality in a dynamic language is only redundant when the operand is boolean-typed; verify before removing"
			m["confidence"] = "low"
		} else {
			m["confidence"] = "high"
		}
		out = append(out, m)
	}
	return out
}

func ConstantReturns(idx *Index) []map[string]any {
	type row struct {
		m         map[string]any
		isTest    bool
		callCount int
	}
	var rows []row
	for name, defs := range idx.defs {
		for _, d := range defs {
			if !d.HasConstRet || suppressedAt(idx, d.Path, d.Line) {
				continue
			}
			// An interface/trait method can't change its signature, so "drop the
			// error return" is not actionable for it.
			if isInterfaceMethod(idx, d) {
				continue
			}
			cc, amb := callCountFor(idx, d)
			m := map[string]any{
				"function": name, "qualified": d.Qualified(), "value": d.ConstReturn,
				"path": d.Path, "line": d.Line, "lang": d.Lang, "exported": d.Exported,
				"call_count": cc, "is_test": d.IsTest,
			}
			if amb {
				m["call_count_ambiguous"] = true
				m["def_count"] = len(defs)
				m["call_count_note"] = "name has several definitions; call_count counts same-directory calls only"
			}
			rows = append(rows, row{m, d.IsTest, cc})
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if sx, sy := scopeRank(rows[a].isTest, false), scopeRank(rows[b].isTest, false); sx != sy {
			return sx < sy
		}
		return rows[a].callCount > rows[b].callCount
	})
	out := make([]map[string]any, len(rows))
	for i, r := range rows {
		out[i] = r.m
	}
	return out
}

func UnexportCandidates(idx *Index) []map[string]any {
	type row struct {
		m         map[string]any
		isTest    bool
		callCount int
	}
	var rows []row
	for name, defs := range idx.defs {
		calls := idx.calls[name]
		if len(calls) == 0 {
			continue
		}
		for _, d := range defs {
			if d.Exported == nil || !*d.Exported || suppressedAt(idx, d.Path, d.Line) {
				continue
			}
			callerDirs := map[string]bool{}
			for _, c := range calls {
				callerDirs[filepath.ToSlash(filepath.Dir(c.Path))] = true
			}
			onlyHere := true
			for dir := range callerDirs {
				if dir != d.Dir {
					onlyHere = false
					break
				}
			}
			if onlyHere && valueRefs(idx, name) == 0 {
				cc, amb := callCountFor(idx, d)
				m := map[string]any{
					"name": name, "qualified": d.Qualified(), "path": d.Path, "line": d.Line,
					"lang": d.Lang, "package_dir": d.Dir, "call_count": cc,
					"note":    "every in-tree caller shares the package; name-based, no symbol resolution",
					"is_test": d.IsTest,
				}
				if amb {
					m["call_count_ambiguous"] = true
					m["def_count"] = len(defs)
				}
				rows = append(rows, row{m, d.IsTest, cc})
			}
		}
	}
	sort.Slice(rows, func(a, b int) bool {
		if sx, sy := scopeRank(rows[a].isTest, false), scopeRank(rows[b].isTest, false); sx != sy {
			return sx < sy
		}
		return rows[a].callCount > rows[b].callCount
	})
	out := make([]map[string]any, len(rows))
	for i, r := range rows {
		out[i] = r.m
	}
	return out
}

func DuplicateBodies(idx *Index, minSize int) []map[string]any {
	if minSize <= 0 {
		minSize = 40
	}
	groups := map[string][]*Def{}
	for _, defs := range idx.defs {
		for _, d := range defs {
			if d.BodySize >= minSize {
				groups[d.BodyHash] = append(groups[d.BodyHash], d)
			}
		}
	}
	var out []map[string]any
	for h, members := range groups {
		if len(members) < 2 {
			continue
		}
		sort.Slice(members, func(a, b int) bool {
			if members[a].Path != members[b].Path {
				return members[a].Path < members[b].Path
			}
			return members[a].Line < members[b].Line
		})
		ms := make([]map[string]any, len(members))
		allTest := true
		for i, m := range members {
			ms[i] = map[string]any{"name": m.Name, "qualified": m.Qualified(), "path": m.Path, "line": m.Line}
			if !m.IsTest {
				allTest = false
			}
		}
		out = append(out, map[string]any{
			"body_hash": h, "count": len(members), "body_size": members[0].BodySize,
			"members": ms, "all_tests": allTest,
		})
	}
	sort.Slice(out, func(a, b int) bool {
		at, bt := out[a]["all_tests"].(bool), out[b]["all_tests"].(bool)
		if at != bt {
			return !at // production groups first
		}
		ca, cb := out[a]["count"].(int), out[b]["count"].(int)
		if ca != cb {
			return ca > cb
		}
		return out[a]["body_size"].(int) > out[b]["body_size"].(int)
	})
	return out
}

// sortFindings sorts []Unused by (confidence, !test, !gen, path, line).
func sortFindings(out []Unused, key func(Unused) (string, bool, bool, string, int)) {
	sort.Slice(out, func(a, b int) bool {
		ca, ta, ga, pa, la := key(out[a])
		cb, tb, gb, pb, lb := key(out[b])
		if confRank(ca) != confRank(cb) {
			return confRank(ca) < confRank(cb)
		}
		if sa, sb := scopeRank(ta, ga), scopeRank(tb, gb); sa != sb {
			return sa < sb
		}
		if pa != pb {
			return pa < pb
		}
		return la < lb
	})
}

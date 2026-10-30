package codefacts

import (
	"context"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/tsutil"
	"github.com/imjasonh/playground/pasta/internal/tswasm"
)

// walkFile parses one file and folds its facts into idx.
func walkFile(ctx context.Context, path, langName string, src []byte, idx *Index, isTest, isGen bool) {
	spec := specs[langName]
	if spec == nil {
		return
	}
	lang := &tswasm.Language{Grammar: spec.grammar}
	tree, root, err := tsutil.Parse(ctx, lang, src, path)
	if err != nil || !root.IsValid() {
		return
	}
	defer tree.Release()
	if tsutil.ErrorHeavy(root) {
		return
	}
	lm := newLineMap(src)
	w := &fileWalk{
		idx: idx, spec: spec, path: path, lang: langName, src: src, lm: lm,
		dir: slashDir(path), isTest: isTest, isGen: isGen,
		fileIdents: map[string]bool{},
	}

	if strings.Contains(string(src), "pasta:ignore") {
		for i, ln := range strings.Split(string(src), "\n") {
			if strings.Contains(ln, "pasta:ignore") {
				if idx.suppressed[path] == nil {
					idx.suppressed[path] = map[int]bool{}
				}
				idx.suppressed[path][i+1] = true
			}
		}
	}

	w.visit(root, -1)

	for _, imp := range w.fileImports {
		if !w.fileIdents[imp.name] {
			idx.unusedImports = append(idx.unusedImports, imp)
		}
	}
}

func slashDir(p string) string {
	if i := strings.LastIndex(p, "/"); i >= 0 {
		return p[:i]
	}
	return "."
}

type fileWalk struct {
	idx           *Index
	spec          *langSpec
	path, lang    string
	src           []byte
	lm            lineMap
	dir           string
	isTest, isGen bool
	fileIdents    map[string]bool
	fileImports   []unusedImport
}

func (w *fileWalk) line(n tsutil.Node) int { return w.lm.line(n.StartByte()) }

func (w *fileWalk) visit(n tsutil.Node, callerID int) {
	t := n.Type()
	spec := w.spec

	if spec.importTypes[t] {
		for _, imp := range w.importBindings(n) {
			w.fileImports = append(w.fileImports, imp)
		}
		return // don't count import-internal idents as uses
	}
	if spec.ifaceDeclTypes[t] {
		w.collectIfaceMethods(n)
		// still recurse so nested defs/calls are seen
	}
	if spec.defTypes[t] {
		d := w.newDef(n)
		for _, c := range n.AllChildren() {
			w.visit(c, d.ID)
		}
		return
	}
	if spec.callTypes[t] {
		w.recordCall(n, callerID)
		for _, c := range n.AllChildren() {
			w.visit(c, callerID)
		}
		return
	}
	if spec.condTypes[t] {
		if v, always, ok := constCondition(w.spec, n.ChildByFieldName(spec.condField)); ok {
			w.idx.dead = append(w.idx.dead, deadBranch{
				construct: t, value: v, always: always, path: w.path, line: w.line(n), lang: w.lang,
			})
		}
	} else if blockTypes[t] {
		w.checkBlock(n)
	} else if identTypes[t] || t == "package_identifier" || t == "namespace_identifier" {
		// package_identifier covers Go/other package-qualified references in type
		// position (e.g. context.Context), where the package name is not a plain
		// identifier — without it, an import used only for types looks unused.
		nm := n.Text()
		w.idx.identUses[nm]++
		w.fileIdents[nm] = true
		s := w.idx.identSites[nm]
		if len(s) < identSiteCap {
			w.idx.identSites[nm] = append(s, site{w.path, w.line(n)})
		}
	} else if stringTypes[t] {
		inner := strings.Trim(strings.TrimSpace(n.Text()), "\"'`")
		if identRe.MatchString(inner) {
			w.idx.stringRefs[inner] = true
		}
	}
	// Redundant comparison to a boolean literal: inspect operands, not text.
	w.checkRedundant(n)

	for _, c := range n.AllChildren() {
		w.visit(c, callerID)
	}
}

// collectIfaceMethods records method names declared in an interface/trait decl;
// their signatures can't change and they are dynamically dispatched.
func (w *fileWalk) collectIfaceMethods(decl tsutil.Node) {
	tsutil.Walk(decl, func(n tsutil.Node) bool {
		t := n.Type()
		if strings.Contains(t, "method") || t == "function_signature_item" ||
			t == "function_item" || t == "abstract_method_declaration" ||
			t == "method_signature" || t == "method_spec" || t == "method_elem" {
			if nm := w.nameOf(n); nm != "" {
				w.idx.ifaceMethods[nm] = true
			}
		}
		return true
	})
}

func (w *fileWalk) nameOf(n tsutil.Node) string {
	if nn := n.ChildByFieldName("name"); nn.IsValid() {
		if id := firstIdent(nn); id != "" {
			return id
		}
		return norm(nn.Text())
	}
	return firstIdent(n)
}

func (w *fileWalk) newDef(n tsutil.Node) *Def {
	spec := w.spec
	name := w.defName(n)
	params := paramNames(n.ChildByFieldName(spec.paramsField))
	body := n.ChildByFieldName(spec.bodyField)
	bf := analyzeBody(body)
	var unused []string
	for _, p := range params {
		if bf.idents[p] || isSelfParam(p) || strings.HasPrefix(p, "arg") || strings.HasPrefix(p, "_") {
			continue
		}
		unused = append(unused, p)
	}
	id := w.idx.nextID
	w.idx.nextID++
	cr, hasCR := constReturn(bf.returns)
	d := &Def{
		ID: id, Name: name, Recv: w.receiverType(n), Params: params, UnusedP: unused,
		Path: w.path, Line: w.line(n), EndLine: w.lm.line(n.EndByte()),
		StartByte: n.StartByte(), EndByte: n.EndByte(),
		Exported: isExported(name, n, spec), Lang: w.lang, Dir: w.dir,
		Branches: bf.branches + 1, Depth: bf.depth, Lines: w.lm.line(n.EndByte()) - w.line(n) + 1,
		BodyHash: bf.typeHash, BodySize: bf.nodeCount, ConstReturn: cr, HasConstRet: hasCR,
		RuntimeRoot: w.runtimeRoot(n, name),
		IsMethod:    strings.Contains(t(n), "method") || inMethodContainer(n),
		IsTest:      w.isTest, IsGenerated: w.isGen,
	}
	w.idx.defs[name] = append(w.idx.defs[name], d)
	w.idx.defsByID[id] = d
	return d
}

func t(n tsutil.Node) string { return n.Type() }

func (w *fileWalk) defName(n tsutil.Node) string {
	nn := n.ChildByFieldName(w.spec.nameField)
	if nn.IsValid() {
		// C/C++ declarator wraps the identifier.
		if id := firstIdent(nn); id != "" {
			return id
		}
		return norm(nn.Text())
	}
	if id := firstIdent(n); id != "" {
		return id
	}
	return "?"
}

// receiverType extracts a method's receiver/owning type, best effort.
func (w *fileWalk) receiverType(n tsutil.Node) string {
	// Go: method_declaration has a `receiver` parameter_list whose single
	// parameter_declaration carries a `type` field (the receiver TYPE, not the
	// receiver variable name).
	if w.spec.recvField != "" {
		if r := n.ChildByFieldName(w.spec.recvField); r.IsValid() {
			for _, pd := range r.NamedChildren() {
				if ty := pd.ChildByFieldName("type"); ty.IsValid() {
					return baseTypeName(ty.Text())
				}
			}
			return baseTypeName(r.Text())
		}
	}
	// Rust/impl & class members: climb to the container and read its type/name.
	p, hops := n.Parent(), 0
	for p.IsValid() && hops < 6 {
		pt := p.Type()
		if pt == "impl_item" {
			if ty := p.ChildByFieldName("type"); ty.IsValid() {
				return baseTypeName(ty.Text())
			}
		}
		if methodContainers[pt] {
			if nm := p.ChildByFieldName("name"); nm.IsValid() {
				return baseTypeName(nm.Text())
			}
		}
		p, hops = p.Parent(), hops+1
	}
	return ""
}

// baseTypeName strips pointers, generics, and lifetimes from a receiver's type
// text and returns the bare identifier (e.g. "*VFSFile" -> "VFSFile").
func baseTypeName(s string) string {
	s = norm(s)
	// take the last identifier-ish token
	s = strings.TrimLeft(s, "*&(")
	for _, cut := range []string{"<", "[", " "} {
		if i := strings.Index(s, cut); i >= 0 {
			s = s[:i]
		}
	}
	if i := strings.LastIndexAny(s, ".:"); i >= 0 {
		s = s[i+1:]
	}
	s = strings.TrimRight(s, ")")
	if identRe.MatchString(s) {
		return s
	}
	// Go receiver text is like "(f *VFSFile)"; pull the trailing word.
	fields := strings.FieldsFunc(s, func(r rune) bool {
		return !(r == '_' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9'))
	})
	if len(fields) > 0 {
		last := fields[len(fields)-1]
		if identRe.MatchString(last) {
			return last
		}
	}
	return ""
}

func (w *fileWalk) recordCall(n tsutil.Node, callerID int) {
	spec := w.spec
	var name, qualifier string
	if spec.calleeNameOnCall != "" {
		if nn := n.ChildByFieldName(spec.calleeNameOnCall); nn.IsValid() {
			name = nn.Text()
		}
		if obj := n.ChildByFieldName("object"); obj.IsValid() {
			qualifier = norm(obj.Text())
		}
	} else {
		fn := n.ChildByFieldName(spec.funcField)
		if !fn.IsValid() {
			return
		}
		if identTypes[fn.Type()] {
			name = fn.Text()
		} else {
			name = trailingName(fn, spec)
			qualifier = qualifierOf(fn)
		}
	}
	if name == "" {
		return
	}
	var args, kinds []string
	if cont := n.ChildByFieldName(spec.argsField); cont.IsValid() {
		for _, c := range cont.NamedChildren() {
			if c.Type() == "comment" {
				continue
			}
			if spec.stopArgTypes[c.Type()] {
				break
			}
			args = append(args, norm(c.Text()))
			kinds = append(kinds, classifyArg(c))
		}
	}
	form := "free"
	if qualifier != "" {
		form = "qualified"
	}
	w.idx.calls[name] = append(w.idx.calls[name], &Call{
		Name: name, Qualifier: qualifier, Form: form, Args: args, Kinds: kinds,
		Path: w.path, Line: w.line(n), Lang: w.lang, CallerID: callerID,
	})
	if callerID < 0 {
		w.idx.toplevelCall[name] = true
	} else {
		if w.idx.callEdges[callerID] == nil {
			w.idx.callEdges[callerID] = map[string]bool{}
		}
		w.idx.callEdges[callerID][name] = true
	}
}

func (w *fileWalk) checkBlock(n tsutil.Node) {
	var stmts []tsutil.Node
	for _, c := range n.NamedChildren() {
		if c.Type() != "comment" {
			stmts = append(stmts, c)
		}
	}
	for i := 0; i+1 < len(stmts); i++ {
		if terminators[stmts[i].Type()] {
			w.idx.unreachable = append(w.idx.unreachable, unreach{
				path: w.path, line: w.line(stmts[i+1]), lang: w.lang, after: stmts[i].Type(),
			})
			break
		}
	}
}

func (w *fileWalk) checkRedundant(n tsutil.Node) {
	t := n.Type()
	if !(strings.Contains(t, "binary") || t == "comparison_operator") {
		return
	}
	op := operatorOf(n)
	if op != "==" && op != "!=" && op != "===" && op != "!==" {
		return
	}
	// one operand must be a bare boolean literal
	var hasBool bool
	for _, c := range n.NamedChildren() {
		bt := strings.ToLower(strings.TrimSpace(c.Text()))
		if bt == "true" || bt == "false" {
			hasBool = true
			break
		}
	}
	if !hasBool || !redundantBoolRe.MatchString(n.Text()) {
		return
	}
	strict := op == "===" || op == "!=="
	dyn := w.lang == "javascript" || w.lang == "typescript" || w.lang == "tsx"
	w.idx.redundant = append(w.idx.redundant, redundant{
		path: w.path, line: w.line(n), lang: w.lang, snippet: trunc(norm(n.Text()), 120),
		kind: "compare-to-boolean-literal", operator: op, strictInDyn: strict && dyn,
	})
}

func trunc(s string, n int) string {
	if len(s) > n {
		return s[:n]
	}
	return s
}

func operatorOf(n tsutil.Node) string {
	if o := n.ChildByFieldName("operator"); o.IsValid() {
		return o.Text()
	}
	for _, c := range n.AllChildren() {
		if c.IsNamed() {
			continue
		}
		switch c.Text() {
		case "==", "!=", "===", "!==":
			return c.Text()
		}
	}
	return ""
}

func (w *fileWalk) runtimeRoot(n tsutil.Node, name string) bool {
	if entrypoints[name] {
		return true
	}
	for _, p := range testPrefixes {
		if strings.HasPrefix(name, p) {
			return true
		}
	}
	// Rust/attribute tests: #[test], #[tokio::test], #[rstest], @Test, ...
	for _, prev := range prevSiblings(n, 6) {
		pt := prev.Type()
		if pt == "attribute_item" || pt == "attribute" || pt == "attribute_list" ||
			pt == "annotation" || pt == "marker_annotation" {
			lt := strings.ToLower(prev.Text())
			if strings.Contains(lt, "test") || strings.Contains(lt, "bench") {
				return true
			}
		} else if pt != "line_comment" && pt != "block_comment" && pt != "comment" {
			break
		}
	}
	return false
}

// prevSiblings returns up to max preceding siblings of n, nearest first.
func prevSiblings(n tsutil.Node, max int) []tsutil.Node {
	p := n.Parent()
	if !p.IsValid() {
		return nil
	}
	kids := p.AllChildren()
	idx := -1
	for i, c := range kids {
		if c.StartByte() == n.StartByte() && c.EndByte() == n.EndByte() && c.Type() == n.Type() {
			idx = i
			break
		}
	}
	if idx < 0 {
		return nil
	}
	var out []tsutil.Node
	for i := idx - 1; i >= 0 && len(out) < max; i-- {
		out = append(out, kids[i])
	}
	return out
}

func inMethodContainer(n tsutil.Node) bool {
	p, hops := n.Parent(), 0
	for p.IsValid() && hops < 8 {
		if methodContainers[p.Type()] {
			return true
		}
		p, hops = p.Parent(), hops+1
	}
	return false
}

func isSelfParam(p string) bool {
	switch p {
	case "self", "this", "cls", "_":
		return true
	}
	return false
}

func qualifierOf(fn tsutil.Node) string {
	for _, f := range qualifierFields {
		if c := fn.ChildByFieldName(f); c.IsValid() {
			return norm(c.Text())
		}
	}
	return ""
}

func trailingName(n tsutil.Node, spec *langSpec) string {
	if !n.IsValid() {
		return ""
	}
	if identTypes[n.Type()] {
		return n.Text()
	}
	for _, f := range spec.calleeNameFields {
		if c := n.ChildByFieldName(f); c.IsValid() {
			if got := trailingName(c, spec); got != "" {
				return got
			}
		}
	}
	kids := n.NamedChildren()
	for i := len(kids) - 1; i >= 0; i-- {
		if identTypes[kids[i].Type()] {
			return kids[i].Text()
		}
	}
	return ""
}

func firstIdent(n tsutil.Node) string {
	if !n.IsValid() {
		return ""
	}
	queue := n.NamedChildren()
	for len(queue) > 0 {
		x := queue[0]
		queue = queue[1:]
		if identTypes[x.Type()] {
			return x.Text()
		}
		queue = append(queue, x.NamedChildren()...)
	}
	return ""
}

func paramNames(cont tsutil.Node) []string {
	if !cont.IsValid() {
		return nil
	}
	var out []string
	for _, c := range cont.NamedChildren() {
		if c.Type() == "comment" {
			continue
		}
		if nm := c.ChildByFieldName("name"); nm.IsValid() && identTypes[nm.Type()] {
			out = append(out, nm.Text())
			continue
		}
		if id := firstIdent(c); id != "" {
			out = append(out, id)
		} else {
			out = append(out, "arg")
		}
	}
	return out
}

func isExported(name string, n tsutil.Node, spec *langSpec) *bool {
	b := func(v bool) *bool { return &v }
	switch spec.exported {
	case "go":
		return b(name != "" && isUpper(name[0]))
	case "python":
		return b(!strings.HasPrefix(name, "_"))
	case "rust":
		return b(hasDescendantType(n, set("visibility_modifier"), 2))
	case "java":
		for _, c := range n.NamedChildren() {
			if c.Type() == "modifiers" {
				return b(strings.Contains(c.Text(), "public"))
			}
		}
		return b(false)
	case "js":
		p, hops := n.Parent(), 0
		for p.IsValid() && hops < 4 {
			if p.Type() == "export_statement" || p.Type() == "export_specifier" {
				return b(true)
			}
			p, hops = p.Parent(), hops+1
		}
		return b(false)
	}
	return nil
}

func hasDescendantType(n tsutil.Node, types map[string]bool, depth int) bool {
	if !n.IsValid() || depth < 0 {
		return false
	}
	for _, c := range n.NamedChildren() {
		if types[c.Type()] || hasDescendantType(c, types, depth-1) {
			return true
		}
	}
	return false
}

type bodyFacts struct {
	idents    map[string]bool
	returns   []retVal
	branches  int
	depth     int
	nodeCount int
	typeHash  string
}
type retVal struct {
	text    string
	literal bool
}

func analyzeBody(body tsutil.Node) bodyFacts {
	idents := map[string]bool{}
	var returns []retVal
	branches, nodeCount, maxDepth := 0, 0, 0
	var seq []string

	var rec func(n tsutil.Node, depth int)
	rec = func(n tsutil.Node, depth int) {
		nodeCount++
		if depth > maxDepth {
			maxDepth = depth
		}
		ty := n.Type()
		seq = append(seq, ty)
		if identTypes[ty] {
			idents[n.Text()] = true
		}
		for _, h := range branchHints {
			if strings.Contains(ty, h) && (strings.Contains(ty, "statement") ||
				strings.Contains(ty, "expression") || strings.Contains(ty, "clause") ||
				strings.HasSuffix(ty, "_when")) {
				branches++
				break
			}
		}
		if returnTypes[ty] {
			var val tsutil.Node
			for _, c := range n.NamedChildren() {
				if c.Type() != "comment" {
					val = c
					break
				}
			}
			if val.IsValid() && val.Type() == "expression_list" && len(val.NamedChildren()) == 1 {
				val = val.NamedChildren()[0]
			}
			if val.IsValid() {
				returns = append(returns, retVal{norm(val.Text()), classifyArg(val) == "literal"})
			} else {
				returns = append(returns, retVal{"", false})
			}
		}
		for _, c := range n.AllChildren() {
			rec(c, depth+1)
		}
	}
	if body.IsValid() {
		rec(body, 0)
	}
	return bodyFacts{idents, returns, branches, maxDepth, nodeCount, sha(seq)}
}

func constReturn(returns []retVal) (string, bool) {
	if len(returns) == 0 {
		return "", false
	}
	var first string
	for i, r := range returns {
		if !r.literal {
			return "", false
		}
		if i == 0 {
			first = r.text
		} else if canonValue(r.text) != canonValue(first) {
			return "", false
		}
	}
	return first, true
}

func (w *fileWalk) importBindings(n tsutil.Node) []unusedImport {
	text := norm(n.Text())
	line := w.line(n)
	var out []unusedImport
	switch w.lang {
	case "go":
		for _, specNode := range descendants(n, set("import_spec")) {
			alias := specNode.ChildByFieldName("name")
			path := specNode.ChildByFieldName("path")
			if !path.IsValid() {
				continue
			}
			raw := strings.Trim(path.Text(), `"`)
			bound := raw
			if alias.IsValid() {
				bound = alias.Text()
			} else {
				name, ok := goImportName(raw)
				if !ok {
					// Package name can't be derived from the path (it diverges,
					// e.g. palette-swap → package palette). Reporting would risk a
					// false positive, so leave it to the compiler.
					continue
				}
				bound = name
			}
			if bound == "_" || bound == "." {
				continue
			}
			out = append(out, unusedImport{name: bound, path: w.path, line: w.line(specNode), lang: w.lang, statement: `import "` + raw + `"`})
		}
	case "python":
		if n.Type() == "import_from_statement" {
			kids := n.NamedChildren()
			var moduleSeen bool
			for _, c := range kids {
				switch c.Type() {
				case "aliased_import":
					if al := c.ChildByFieldName("alias"); al.IsValid() {
						out = append(out, unusedImport{name: al.Text(), path: w.path, line: line, lang: w.lang, statement: text})
					} else if nm := c.ChildByFieldName("name"); nm.IsValid() {
						out = append(out, unusedImport{name: firstSeg(nm.Text(), "."), path: w.path, line: line, lang: w.lang, statement: text})
					}
				case "dotted_name":
					if !moduleSeen {
						moduleSeen = true
						continue // module being imported from
					}
					out = append(out, unusedImport{name: lastSeg(c.Text(), "."), path: w.path, line: line, lang: w.lang, statement: text})
				}
			}
		} else { // import_statement
			for _, c := range n.NamedChildren() {
				switch c.Type() {
				case "aliased_import":
					if al := c.ChildByFieldName("alias"); al.IsValid() {
						out = append(out, unusedImport{name: al.Text(), path: w.path, line: line, lang: w.lang, statement: text})
					}
				case "dotted_name":
					out = append(out, unusedImport{name: firstSeg(c.Text(), "."), path: w.path, line: line, lang: w.lang, statement: text})
				}
			}
		}
	}
	return out
}

// goImportName derives the default identifier a Go import binds, without an
// explicit alias. It mirrors the common cases the package clause would resolve:
// a trailing major-version segment (math/rand/v2 → rand, go.yaml.in/yaml/v3 →
// yaml) is dropped, as are the go-/-go module-name conventions (go-git → git,
// go-envconfig → envconfig). It is a heuristic; when it is wrong the file still
// compiles, so an alias always wins over this guess.
func goImportName(raw string) (string, bool) {
	segs := strings.Split(raw, "/")
	last := segs[len(segs)-1]
	if versionSeg.MatchString(last) && len(segs) >= 2 {
		last = segs[len(segs)-2]
	}
	if i := strings.LastIndex(last, "."); i >= 0 && versionSeg.MatchString(last[i+1:]) {
		last = last[:i]
	}
	last = strings.TrimSuffix(last, ".go")
	last = strings.TrimPrefix(last, "go-")
	last = strings.TrimSuffix(last, "-go")
	// A remaining hyphen or dot means the package name diverges from the path
	// segment and can't be known without the package clause; report unreliable.
	if strings.ContainsAny(last, "-.") || last == "" {
		return "", false
	}
	return last, true
}

func firstSeg(s, sep string) string {
	if i := strings.Index(s, sep); i >= 0 {
		return s[:i]
	}
	return s
}
func lastSeg(s, sep string) string {
	if i := strings.LastIndex(s, sep); i >= 0 {
		return s[i+1:]
	}
	return s
}

func descendants(n tsutil.Node, types map[string]bool) []tsutil.Node {
	var out []tsutil.Node
	tsutil.Walk(n, func(x tsutil.Node) bool {
		if types[x.Type()] {
			out = append(out, x)
		}
		return true
	})
	return out
}

func constCondition(spec *langSpec, cond tsutil.Node) (string, bool, bool) {
	if !cond.IsValid() {
		return "", false, false
	}
	for parenTypes[cond.Type()] && len(cond.NamedChildren()) == 1 {
		cond = cond.NamedChildren()[0]
	}
	txt := strings.TrimSpace(cond.Text())
	switch strings.ToLower(txt) {
	case "true":
		return "true", true, true
	case "false":
		return "false", false, true
	}
	switch txt {
	case "1":
		return "1", true, true
	case "0":
		return "0", false, true
	}
	return "", false, false
}

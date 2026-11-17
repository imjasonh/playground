// Package codefacts indexes a source tree into a call graph plus a
// symbol/reference index, then answers composable fact queries and runs
// non-deterministic cleanup sweeps (unused code, constant arguments, dead
// branches, and more) over the result.
//
// It is the engine behind pasta's agent-facing MCP server: where the CUE
// analyzers are deterministic single-rule checks, codefacts gives an agent the
// AST facts to judge cleanups that need taste (a uniform in-tree caller set for
// an exported API is a signal to add tests, not strip an argument).
//
// Binding is by callee name (with a recorded qualifier) and arity, not by
// resolved symbol identity: tree-sitter has no name resolution or types. The
// imprecision is reported, never hidden — findings carry export status,
// call-graph reachability, name collisions, and a confidence tier so a caller
// judges rather than trusts. The engine reuses pasta's wazero-hosted tree-sitter
// runtime (internal/treesitter), so it is pure Go and CGO-free.
package codefacts

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/imjasonh/playground/pasta/internal/testpath"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// langSpec describes the tree-sitter node vocabulary codefacts needs for one
// language. Node-type names come from each grammar.
type langSpec struct {
	name             string
	grammar          string
	exts             []string
	callTypes        map[string]bool
	defTypes         map[string]bool
	argsField        string
	funcField        string
	calleeNameOnCall string // java/ruby: callee name is a field of the call node
	calleeNameFields []string
	nameField        string
	paramsField      string
	bodyField        string
	recvField        string // method receiver field (go: receiver)
	stopArgTypes     map[string]bool
	exported         string
	condTypes        map[string]bool
	condField        string
	importTypes      map[string]bool
	ifaceDeclTypes   map[string]bool // interface/trait decls whose method names can't change
}

func set(xs ...string) map[string]bool {
	m := make(map[string]bool, len(xs))
	for _, x := range xs {
		m[x] = true
	}
	return m
}

var specs = map[string]*langSpec{
	"go": {
		name: "go", grammar: "go", exts: []string{".go"},
		callTypes: set("call_expression"),
		defTypes:  set("function_declaration", "method_declaration"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"field"}, nameField: "name",
		paramsField: "parameters", bodyField: "body", recvField: "receiver",
		exported: "go", condTypes: set("if_statement"), condField: "condition",
		importTypes: set("import_declaration"), ifaceDeclTypes: set("interface_type"),
	},
	"python": {
		name: "python", grammar: "python", exts: []string{".py"},
		callTypes: set("call"), defTypes: set("function_definition"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"attribute"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		stopArgTypes: set("keyword_argument", "dictionary_splat", "list_splat"),
		exported:     "python", condTypes: set("if_statement", "elif_clause"), condField: "condition",
		importTypes: set("import_statement", "import_from_statement"),
	},
	"javascript": {
		name: "javascript", grammar: "javascript",
		exts:      []string{".js", ".jsx", ".mjs", ".cjs"},
		callTypes: set("call_expression"),
		defTypes:  set("function_declaration", "method_definition"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"property"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		stopArgTypes: set("spread_element"),
		exported:     "js", condTypes: set("if_statement"), condField: "condition",
	},
	"typescript": {
		name: "typescript", grammar: "typescript", exts: []string{".ts"},
		callTypes: set("call_expression"),
		defTypes:  set("function_declaration", "method_definition"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"property"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		stopArgTypes: set("spread_element"),
		exported:     "js", condTypes: set("if_statement"), condField: "condition",
		ifaceDeclTypes: set("interface_declaration", "object_type"),
	},
	"tsx": {
		name: "tsx", grammar: "tsx", exts: []string{".tsx"},
		callTypes: set("call_expression"),
		defTypes:  set("function_declaration", "method_definition"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"property"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		stopArgTypes: set("spread_element"),
		exported:     "js", condTypes: set("if_statement"), condField: "condition",
		ifaceDeclTypes: set("interface_declaration", "object_type"),
	},
	"rust": {
		name: "rust", grammar: "rust", exts: []string{".rs"},
		callTypes: set("call_expression"), defTypes: set("function_item"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"field", "name"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		exported: "rust", condTypes: set("if_expression"), condField: "condition",
		ifaceDeclTypes: set("trait_item"),
	},
	"java": {
		name: "java", grammar: "java", exts: []string{".java"},
		callTypes: set("method_invocation"), defTypes: set("method_declaration"),
		argsField: "arguments", calleeNameOnCall: "name", nameField: "name",
		paramsField: "parameters", bodyField: "body",
		exported: "java", condTypes: set("if_statement"), condField: "condition",
		ifaceDeclTypes: set("interface_declaration"),
	},
	"c": {
		name: "c", grammar: "c", exts: []string{".c", ".h"},
		callTypes: set("call_expression"), defTypes: set("function_definition"),
		argsField: "arguments", funcField: "function", nameField: "declarator",
		paramsField: "parameters", bodyField: "body",
		condTypes: set("if_statement"), condField: "condition",
	},
	"cpp": {
		name: "cpp", grammar: "cpp", exts: []string{".cc", ".cpp", ".cxx", ".hpp", ".hh"},
		callTypes: set("call_expression"), defTypes: set("function_definition"),
		argsField: "arguments", funcField: "function", nameField: "declarator",
		calleeNameFields: []string{"field", "name"},
		paramsField:      "parameters", bodyField: "body",
		condTypes: set("if_statement"), condField: "condition",
	},
	"ruby": {
		name: "ruby", grammar: "ruby", exts: []string{".rb"},
		callTypes: set("call", "method_call", "command", "command_call"),
		defTypes:  set("method", "singleton_method"),
		argsField: "arguments", calleeNameOnCall: "method", nameField: "name",
		paramsField: "parameters", bodyField: "body",
		condTypes: set("if"), condField: "condition",
	},
	"php": {
		name: "php", grammar: "php", exts: []string{".php"},
		callTypes: set("function_call_expression", "member_call_expression", "scoped_call_expression"),
		defTypes:  set("function_definition", "method_declaration"),
		argsField: "arguments", funcField: "function",
		calleeNameFields: []string{"name"}, nameField: "name",
		paramsField: "parameters", bodyField: "body",
		condTypes: set("if_statement"), condField: "condition",
		ifaceDeclTypes: set("interface_declaration"),
	},
}

var extToLang = func() map[string]string {
	m := map[string]string{}
	for name, s := range specs {
		for _, e := range s.exts {
			m[e] = name
		}
	}
	return m
}()

// SupportedLanguages returns the registered language names, sorted.
func SupportedLanguages() []string {
	out := make([]string, 0, len(specs))
	for n := range specs {
		out = append(out, n)
	}
	sort.Strings(out)
	return out
}

var skipDirs = set(
	".git", "node_modules", "vendor", "target", "dist", "build", ".venv",
	"venv", "__pycache__", "testdata", "DerivedData", ".pasta",
)

var identTypes = set(
	"identifier", "type_identifier", "field_identifier", "constant",
	"simple_identifier", "shorthand_property_identifier",
)
var literalWords = set("true", "false", "nil", "null", "none", "undefined")
var literalSubstr = []string{"literal", "string", "number", "integer", "float", "char", "boolean", "rune"}
var stringTypes = set(
	"string", "string_literal", "interpreted_string_literal", "raw_string_literal",
	"string_content", "string_fragment", "quoted_string", "char_literal",
	"verbatim_string_literal",
)
var methodContainers = set(
	"impl_item", "trait_item", "class_body", "class_definition",
	"class_declaration", "class_specifier", "struct_specifier",
	"object_declaration", "interface_declaration", "interface_body",
	"trait_declaration", "object_definition", "template", "protocol_declaration",
)
var qualifiedTypes = set(
	"selector_expression", "scoped_identifier", "attribute", "field_expression",
	"member_expression", "qualified_identifier", "scoped_type_identifier",
)
var qualifierFields = []string{"operand", "object", "value", "path", "receiver"}
var parenTypes = set("parenthesized_expression", "parenthesized")
var blockTypes = set("block", "statement_block", "suite", "compound_statement")
var terminators = set(
	"return_statement", "raise_statement", "throw_statement", "break_statement",
	"continue_statement", "return_expression", "goto_statement",
)
var returnTypes = set("return_statement", "return_expression")
var branchHints = []string{"if", "for", "while", "case", "catch", "switch", "when", "and", "or"}
var entrypoints = set("main", "init", "__init__", "__main__", "setUp", "tearDown", "TestMain")
var testPrefixes = []string{"Test", "Benchmark", "Example", "Fuzz", "test_"}

// goStdlibIfaceMethods are method names that very commonly satisfy a standard-
// library interface not declared in the tree (io.Closer, error, fmt.Stringer,
// http.Handler, …). A method with one of these names can't change its signature
// and is usually dynamically dispatched, so const-return / unused-param findings
// on it are noise. Applied to Go methods only.
var goStdlibIfaceMethods = set(
	"Close", "Error", "String", "Read", "Write", "ServeHTTP", "Len", "Less",
	"Swap", "MarshalJSON", "UnmarshalJSON", "Scan", "Value", "Next", "Seek",
	"Flush", "Reset", "Done", "Err", "Unwrap", "Format", "Name",
)

var identRe = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_]*$`)
var versionSeg = regexp.MustCompile(`^v[0-9]+$`)
var redundantBoolRe = regexp.MustCompile(`(?i)(true|false)`)

var generatedMarkers = []string{
	"Code generated", "DO NOT EDIT", "@generated", "autogenerated", "Generated by",
	"go:generate", "Code generated by",
}

func norm(s string) string { return strings.Join(strings.Fields(s), " ") }

func canonValue(text string) string {
	switch strings.ToLower(text) {
	case "null", "none", "nil":
		return "nil"
	}
	return text
}

func classifyArg(n tsutil.Node) argKind {
	t := n.Type()
	if literalWords[t] {
		return argLiteral
	}
	for _, s := range literalSubstr {
		if strings.Contains(t, s) {
			return argLiteral
		}
	}
	if identTypes[t] {
		txt := n.Text()
		if literalWords[txt] {
			return argLiteral
		}
		if txt != "" && (isUpper(txt[0]) || txt == strings.ToUpper(txt)) {
			return argConst
		}
		return argIdent
	}
	if qualifiedTypes[t] {
		return argConst
	}
	return argExpr
}

func isUpper(b byte) bool { return b >= 'A' && b <= 'Z' }

// call is one call site, bound by callee name (its key in Index.calls) and an
// optional qualifier. A large tree has millions of them, so a call holds no
// pointers and the garbage collector never scans them: strings live in
// Index.strs, arguments in Index.args, and the file in Index.srcFiles.
type call struct {
	qualifier strID
	file      uint32 // index into Index.srcFiles
	line      int32
	callerID  int32  // -1 at file top level
	args      uint32 // offset of the first argument in Index.args
	nargs     uint32
}

// form reports whether the call names its callee alone or through a
// qualifier.
func (c call) form() string {
	if c.qualifier != 0 {
		return "qualified"
	}
	return "free"
}

// strID indexes Index.strs. The zero ID is the empty string.
type strID uint32

// callArg is one argument of a call: its normalized text and its kind.
type callArg struct {
	value strID
	kind  argKind
}

type argKind uint8

const (
	argExpr argKind = iota
	argLiteral
	argConst
	argIdent
)

func (k argKind) String() string {
	switch k {
	case argLiteral:
		return "literal"
	case argConst:
		return "const"
	case argIdent:
		return "ident"
	default:
		return "expr"
	}
}

// srcFile is a file that contributed calls to the index.
type srcFile struct {
	path, dir, lang string
}

// Def is one function/method definition.
type Def struct {
	ID          int
	Name        string
	Recv        string // method receiver type, e.g. "VFSFile" (best effort)
	Params      []string
	UnusedP     []string
	Path        string
	Line        int
	EndLine     int
	StartByte   uint32
	EndByte     uint32
	Exported    *bool
	Lang        string
	Dir         string
	Branches    int
	Depth       int
	Lines       int
	BodyHash    string
	BodySize    int
	ConstReturn string // literal every return yields, else ""
	HasConstRet bool
	RuntimeRoot bool // invoked by a runtime/test harness, not by name
	IsMethod    bool
	IsTest      bool
	IsGenerated bool
}

// Qualified returns "Recv.Name" when a receiver is known, else Name.
func (d *Def) Qualified() string {
	if d.Recv != "" {
		return d.Recv + "." + d.Name
	}
	return d.Name
}

type deadBranch struct {
	construct, value, path, lang string
	always                       bool
	line                         int
}
type unreach struct {
	path, lang, after string
	line              int
}
type unusedImport struct {
	name, path, lang, statement string
	line                        int
}
type redundant struct {
	path, lang, snippet, kind, operator string
	line                                int
	strictInDyn                         bool
}

// Index is the indexed view of a source tree.
type Index struct {
	calls         map[string][]call
	strs          []string
	strIDs        map[string]strID
	args          []callArg
	srcFiles      []srcFile
	defs          map[string][]*Def
	defsByID      map[int]*Def
	identUses     map[string]int
	identSites    map[string][]site
	callEdges     map[int]map[string]bool
	toplevelCall  map[string]bool
	dead          []deadBranch
	unreachable   []unreach
	unusedImports []unusedImport
	redundant     []redundant
	suppressed    map[string]map[int]bool
	stringRefs    map[string]bool
	ifaceMethods  map[string]bool
	files         int
	filesByLang   map[string]int
	langs         map[string]bool
	nextID        int
}

type site struct {
	path string
	line int
}

const identSiteCap = 400

func newIndex() *Index {
	return &Index{
		calls: map[string][]call{}, strs: []string{""}, strIDs: map[string]strID{"": 0},
		defs: map[string][]*Def{}, defsByID: map[int]*Def{},
		identUses: map[string]int{}, identSites: map[string][]site{},
		callEdges: map[int]map[string]bool{}, toplevelCall: map[string]bool{},
		suppressed: map[string]map[int]bool{}, stringRefs: map[string]bool{},
		ifaceMethods: map[string]bool{}, filesByLang: map[string]int{}, langs: map[string]bool{},
	}
}

// intern returns the ID of s in idx.strs, adding s if it is new.
func (idx *Index) intern(s string) strID {
	if id, ok := idx.strIDs[s]; ok {
		return id
	}
	id := strID(len(idx.strs))
	idx.strs = append(idx.strs, s)
	idx.strIDs[s] = id
	return id
}

func (idx *Index) str(id strID) string { return idx.strs[id] }

func (idx *Index) callArgs(c call) []callArg { return idx.args[c.args : c.args+c.nargs] }

// argValues returns the text of c's arguments, or nil when it has none.
func (idx *Index) argValues(c call) []string {
	if c.nargs == 0 {
		return nil
	}
	out := make([]string, c.nargs)
	for i, a := range idx.callArgs(c) {
		out[i] = idx.str(a.value)
	}
	return out
}

func (idx *Index) callFile(c call) *srcFile { return &idx.srcFiles[c.file] }

// BuildOptions scopes a Build.
type BuildOptions struct {
	Langs        []string // limit to these language names; empty = all
	Exclude      []string // slash-path globs to drop (matched against the path and every suffix)
	IncludeTests bool     // when false, test-convention files are skipped entirely
	IncludeGen   bool     // when false, generated files are skipped entirely
	MaxFileSize  int64    // bytes; 0 = default 2 MiB
}

// Default build options: include everything, 2 MiB cap.
func DefaultBuildOptions() BuildOptions {
	return BuildOptions{IncludeTests: true, IncludeGen: true, MaxFileSize: 2 << 20}
}

// Build walks each root, parses every file whose extension maps to a supported
// language, and returns the index.
//
// Files are parsed in parallel, each into its own index, and merged in walk
// order, so the result doesn't depend on which parse finishes first.
func Build(ctx context.Context, roots []string, opts BuildOptions) (*Index, error) {
	if opts.MaxFileSize == 0 {
		opts.MaxFileSize = 2 << 20
	}
	var want map[string]bool
	if len(opts.Langs) > 0 {
		want = set(opts.Langs...)
	}
	var cands []candidate
	for _, root := range roots {
		info, err := os.Stat(root)
		if err != nil {
			return nil, err
		}
		if !info.IsDir() {
			cands = appendCandidate(cands, root, root, want, opts)
			continue
		}
		err = filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() {
				if p != root && skipDirs[d.Name()] {
					return filepath.SkipDir
				}
				return nil
			}
			if d.Type()&fs.ModeSymlink != 0 {
				return nil
			}
			cands = appendCandidate(cands, p, root, want, opts)
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	return buildAll(ctx, cands, opts)
}

// candidate is a file the walk selected by its path, before it is read.
type candidate struct {
	path, rel, abs, lang string
}

func appendCandidate(cands []candidate, p, root string, want map[string]bool, opts BuildOptions) []candidate {
	langName := extToLang[strings.ToLower(filepath.Ext(p))]
	if langName == "" || (want != nil && !want[langName]) {
		return cands
	}
	rel := relOf(p, root)
	if matchesAny(rel, opts.Exclude) {
		return cands
	}
	abs, _ := filepath.Abs(p)
	return append(cands, candidate{path: p, rel: rel, abs: abs, lang: langName})
}

// maxChunk caps the consecutive files one worker indexes and merges before
// handing the result to the in-order merge.
const maxChunk = 64

// buildAll indexes cands on a worker pool and merges the per-file indexes in
// candidate order. A file reached through two roots counts once, under the
// first root that accepts it.
//
// Merging is associative over consecutive files, so each worker merges a
// chunk of consecutive candidates and the caller merges whole chunks in
// order. A slow file then holds back only the chunks behind it, and most of
// the merging runs on the workers.
func buildAll(ctx context.Context, cands []candidate, opts BuildOptions) (*Index, error) {
	cands = dedupeCandidates(cands, opts)
	workers := max(1, min(runtime.GOMAXPROCS(0), len(cands)))
	// Aim for 16 chunks per worker so the pool stays balanced at the end.
	chunk := min(maxChunk, max(1, len(cands)/(16*workers)))
	results := make([]chan *Index, (len(cands)+chunk-1)/chunk)
	for i := range results {
		results[i] = make(chan *Index, 1)
	}
	// window bounds the chunks that are indexing or waiting to merge, so a
	// slow file early in the walk doesn't buffer every later index.
	window := make(chan struct{}, 16*workers)
	var next atomic.Int64
	var wg sync.WaitGroup
	for range workers {
		wg.Go(func() {
			for {
				select {
				case window <- struct{}{}:
				case <-ctx.Done():
					return
				}
				k := int(next.Add(1)) - 1
				if k >= len(results) {
					<-window
					return
				}
				idx := newIndex()
				for _, c := range cands[k*chunk : min((k+1)*chunk, len(cands))] {
					if f := indexFile(ctx, c, opts); f != nil {
						idx.merge(f)
					}
				}
				results[k] <- idx
			}
		})
	}
	defer wg.Wait()

	idx := newIndex()
	for _, r := range results {
		select {
		case f := <-r:
			idx.merge(f)
		case <-ctx.Done():
			return nil, ctx.Err()
		}
		<-window
	}
	return idx, nil
}

// dedupeCandidates keeps one candidate per file: the first whose path passes
// the test-file filter. Size and generated-file checks read the file itself,
// so they agree for every path to it.
func dedupeCandidates(cands []candidate, opts BuildOptions) []candidate {
	accepted := make(map[string]bool, len(cands))
	out := make([]candidate, 0, len(cands))
	for _, c := range cands {
		if accepted[c.abs] || (!opts.IncludeTests && testpath.Is(c.rel)) {
			continue
		}
		accepted[c.abs] = true
		out = append(out, c)
	}
	return out
}

func relOf(p, root string) string {
	if rel, err := filepath.Rel(root, p); err == nil {
		return filepath.ToSlash(rel)
	}
	return filepath.ToSlash(p)
}

// indexFile reads and walks one candidate into a fresh index. It returns nil
// when the file is filtered out.
func indexFile(ctx context.Context, c candidate, opts BuildOptions) *Index {
	fi, err := os.Stat(c.path)
	if err != nil || fi.Size() > opts.MaxFileSize {
		return nil
	}
	src, err := os.ReadFile(c.path)
	if err != nil {
		return nil
	}
	isTest := testpath.Is(c.rel)
	if isTest && !opts.IncludeTests {
		return nil
	}
	isGen := isGenerated(src)
	if isGen && !opts.IncludeGen {
		return nil
	}
	idx := newIndex()
	walkFile(ctx, c.rel, c.lang, src, idx, isTest, isGen)
	idx.files = 1
	idx.filesByLang[c.lang] = 1
	idx.langs[c.lang] = true
	return idx
}

// merge folds f, the index of one file, into idx. f's definition IDs are
// shifted past idx's, and f must not be used afterward.
func (idx *Index) merge(f *Index) {
	off := idx.nextID
	for name, ds := range f.defs {
		for _, d := range ds {
			d.ID += off
			idx.defsByID[d.ID] = d
		}
		idx.defs[name] = append(idx.defs[name], ds...)
	}
	strMap := make([]strID, len(f.strs))
	for i, s := range f.strs {
		strMap[i] = idx.intern(s)
	}
	fileOff := uint32(len(idx.srcFiles))
	idx.srcFiles = append(idx.srcFiles, f.srcFiles...)
	argOff := uint32(len(idx.args))
	for _, a := range f.args {
		idx.args = append(idx.args, callArg{value: strMap[a.value], kind: a.kind})
	}
	for name, cs := range f.calls {
		for i := range cs {
			c := &cs[i]
			c.qualifier = strMap[c.qualifier]
			c.file += fileOff
			c.args += argOff
			if c.callerID >= 0 {
				c.callerID += int32(off)
			}
		}
		idx.calls[name] = append(idx.calls[name], cs...)
	}
	for id, names := range f.callEdges {
		idx.callEdges[id+off] = names
	}
	idx.nextID += f.nextID
	for name, n := range f.identUses {
		idx.identUses[name] += n
	}
	for name, sites := range f.identSites {
		s := idx.identSites[name]
		if room := identSiteCap - len(s); room > 0 {
			idx.identSites[name] = append(s, sites[:min(room, len(sites))]...)
		}
	}
	unionInto(idx.toplevelCall, f.toplevelCall)
	unionInto(idx.stringRefs, f.stringRefs)
	unionInto(idx.ifaceMethods, f.ifaceMethods)
	unionInto(idx.langs, f.langs)
	for path, lines := range f.suppressed {
		if idx.suppressed[path] == nil {
			idx.suppressed[path] = lines
			continue
		}
		unionInto(idx.suppressed[path], lines)
	}
	idx.dead = append(idx.dead, f.dead...)
	idx.unreachable = append(idx.unreachable, f.unreachable...)
	idx.unusedImports = append(idx.unusedImports, f.unusedImports...)
	idx.redundant = append(idx.redundant, f.redundant...)
	idx.files += f.files
	for lang, n := range f.filesByLang {
		idx.filesByLang[lang] += n
	}
}

func unionInto[K comparable](dst, src map[K]bool) {
	for k, v := range src {
		if v {
			dst[k] = true
		}
	}
}

func isGenerated(src []byte) bool {
	head := src
	if len(head) > 2048 {
		head = head[:2048]
	}
	s := string(head)
	for _, m := range generatedMarkers {
		if strings.Contains(s, m) {
			return true
		}
	}
	return false
}

// matchesAny reports whether path (or any of its trailing path segments) matches
// one of the slash-globs. "**" matches zero or more path segments.
func matchesAny(path string, globs []string) bool {
	if len(globs) == 0 {
		return false
	}
	candidates := []string{path}
	for i := 0; i < len(path); i++ {
		if path[i] == '/' {
			candidates = append(candidates, path[i+1:])
		}
	}
	for _, g := range globs {
		for _, c := range candidates {
			if globMatch(g, c) {
				return true
			}
		}
	}
	return false
}

func globMatch(pattern, name string) bool {
	if strings.Contains(pattern, "**") {
		// Translate ** to a regexp; * matches within a segment.
		re := "^" + regexp.QuoteMeta(pattern) + "$"
		re = strings.ReplaceAll(re, `\*\*/`, `(.*/)?`)
		re = strings.ReplaceAll(re, `\*\*`, `.*`)
		re = strings.ReplaceAll(re, `\*`, `[^/]*`)
		ok, _ := regexp.MatchString(re, name)
		return ok
	}
	ok, _ := filepath.Match(pattern, name)
	return ok
}

// lineMap computes 1-based line numbers from byte offsets.
type lineMap []int // byte offsets of each '\n'

func newLineMap(src []byte) lineMap {
	var lm lineMap
	for i, b := range src {
		if b == '\n' {
			lm = append(lm, i)
		}
	}
	return lm
}

func (lm lineMap) line(off uint32) int {
	o := int(off)
	return 1 + sort.Search(len(lm), func(i int) bool { return lm[i] >= o })
}

func sha(parts []string) string {
	h := sha256.New()
	for _, p := range parts {
		h.Write([]byte(p))
		h.Write([]byte{0x1f})
	}
	return hex.EncodeToString(h.Sum(nil))[:24]
}

func suppressedAt(idx *Index, path string, line int) bool {
	s := idx.suppressed[path]
	return s != nil && s[line]
}

func valueRefs(idx *Index, name string) int {
	n := idx.identUses[name] - len(idx.calls[name]) - len(idx.defs[name])
	if n < 0 {
		return 0
	}
	return n
}

// sameDirCalls counts calls to name whose call site shares dir. It is a proxy
// for same-package/local calls when a name has several definitions, so a name-
// global count isn't reported as if it belonged to one definition.
func sameDirCalls(idx *Index, name, dir string) int {
	n := 0
	for _, c := range idx.calls[name] {
		if idx.callFile(c).dir == dir {
			n++
		}
	}
	return n
}

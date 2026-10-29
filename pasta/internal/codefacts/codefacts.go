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
// runtime (internal/tswasm), so it is pure Go and CGO-free.
package codefacts

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

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

// testPathRe matches files that are test code by path convention.
var testPathRe = regexp.MustCompile(
	`(^|/)(tests?|__tests__|testdata|spec|specs|e2e)(/)|(_test\.(go|rs|py))$|(\.test\.|\.spec\.|_test\.|_spec\.|test_[^/]*\.py$)`)

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

func classifyArg(n tsutil.Node) string {
	t := n.Type()
	if literalWords[t] {
		return "literal"
	}
	for _, s := range literalSubstr {
		if strings.Contains(t, s) {
			return "literal"
		}
	}
	if identTypes[t] {
		txt := n.Text()
		if literalWords[txt] {
			return "literal"
		}
		if txt != "" && (isUpper(txt[0]) || txt == strings.ToUpper(txt)) {
			return "const"
		}
		return "ident"
	}
	if qualifiedTypes[t] {
		return "const"
	}
	return "expr"
}

func isUpper(b byte) bool { return b >= 'A' && b <= 'Z' }

// Call is one call site, bound by callee name + optional qualifier.
type Call struct {
	Name      string
	Qualifier string
	Form      string // free | qualified
	Args      []string
	Kinds     []string
	Path      string
	Line      int
	Lang      string
	CallerID  int // -1 at file top level
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
	calls         map[string][]*Call
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
		calls: map[string][]*Call{}, defs: map[string][]*Def{}, defsByID: map[int]*Def{},
		identUses: map[string]int{}, identSites: map[string][]site{},
		callEdges: map[int]map[string]bool{}, toplevelCall: map[string]bool{},
		suppressed: map[string]map[int]bool{}, stringRefs: map[string]bool{},
		ifaceMethods: map[string]bool{}, filesByLang: map[string]int{}, langs: map[string]bool{},
	}
}

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
func Build(ctx context.Context, roots []string, opts BuildOptions) (*Index, error) {
	if opts.MaxFileSize == 0 {
		opts.MaxFileSize = 2 << 20
	}
	var want map[string]bool
	if len(opts.Langs) > 0 {
		want = set(opts.Langs...)
	}
	idx := newIndex()
	seen := map[string]bool{}
	for _, root := range roots {
		info, err := os.Stat(root)
		if err != nil {
			return nil, err
		}
		if !info.IsDir() {
			if err := buildFile(ctx, root, root, want, opts, idx, seen); err != nil {
				return nil, err
			}
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
			return buildFile(ctx, p, root, want, opts, idx, seen)
		})
		if err != nil {
			return nil, err
		}
	}
	return idx, nil
}

func relOf(p, root string) string {
	if rel, err := filepath.Rel(root, p); err == nil {
		return filepath.ToSlash(rel)
	}
	return filepath.ToSlash(p)
}

func buildFile(ctx context.Context, p, root string, want map[string]bool, opts BuildOptions, idx *Index, seen map[string]bool) error {
	abs, _ := filepath.Abs(p)
	if seen[abs] {
		return nil
	}
	langName := extToLang[strings.ToLower(filepath.Ext(p))]
	if langName == "" || (want != nil && !want[langName]) {
		return nil
	}
	rel := relOf(p, root)
	if matchesAny(rel, opts.Exclude) {
		return nil
	}
	fi, err := os.Stat(p)
	if err != nil || fi.Size() > opts.MaxFileSize {
		return nil
	}
	src, err := os.ReadFile(p)
	if err != nil {
		return nil
	}
	isTest := testPathRe.MatchString(rel)
	if isTest && !opts.IncludeTests {
		return nil
	}
	isGen := isGenerated(src)
	if isGen && !opts.IncludeGen {
		return nil
	}
	seen[abs] = true
	walkFile(ctx, rel, langName, src, idx, isTest, isGen)
	idx.files++
	idx.filesByLang[langName]++
	idx.langs[langName] = true
	return nil
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
		if filepath.ToSlash(filepath.Dir(c.Path)) == dir {
			n++
		}
	}
	return n
}

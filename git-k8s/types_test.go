package gitk8s

import (
	"cmp"
	"encoding/json"
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/types"
)

var labelValueRE = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]*[a-z0-9])?$`)

func TestBranchObjectName(t *testing.T) {
	names := []string{
		BranchObjectName("app", "main"),
		BranchObjectName("app", "c/add"),
		BranchObjectName("app", "c-add"),
		BranchObjectName("app", "C/Add"),
		BranchObjectName("app", strings.Repeat("x", 300)),
		BranchObjectName("app", "///"),
		BranchObjectName("my.repo", "feature/ünïcode"),
	}
	seen := map[string]bool{}
	for _, n := range names {
		if len(n) > 63 || !labelValueRE.MatchString(n) {
			t.Errorf("%q isn't a valid object name and label value", n)
		}
		if seen[n] {
			t.Errorf("%q appears twice", n)
		}
		seen[n] = true
	}
	if !strings.HasPrefix(names[1], "app-c-add-") {
		t.Errorf("name for c/add = %q, want prefix app-c-add-", names[1])
	}
	if names[1] != BranchObjectName("app", "c/add") {
		t.Error("BranchObjectName isn't deterministic")
	}
}

// The API server matches a CustomResourceDefinition's patterns with Go's
// regexp package, so this is what it accepts.
func TestURLPattern(t *testing.T) {
	field, _ := reflect.TypeFor[RepositorySpec]().FieldByName("URL")
	pattern := regexp.MustCompile(field.Tag.Get("pattern"))
	for _, u := range []string{
		"https://git.example.com/app.git",
		"http://172.18.0.1:18418/app.git",
		"https://[2001:db8::1]/app.git",
		"https://git-k8s@git.example.com/app.git",
		"https://first.last%40example.com@git.example.com/org/app.git",
	} {
		if !pattern.MatchString(u) {
			t.Errorf("the pattern rejects %q", u)
		}
	}
	for _, u := range []string{
		"git://git.example.com/app.git",
		"ssh://git@git.example.com:2222/app.git",
		"ssh://example.com/~/app.git",
		"git@github.com:imjasonh/playground.git",
		"git@[172.18.0.1:2222]:app.git",
		"https://git.example.com/app.git?ref=main",
		"https://git.example.com/app.git#main",
		"https://git-k8s?@git.example.com/app.git",
		"--upload-pack=touch /tmp/pwned",
		"-oProxyCommand=touch /tmp/pwned",
		"ext::sh -c touch% /tmp/pwned",
		"fd::3",
		"s3://bucket/app.git",
		"HTTPS://git.example.com/app.git",
		"git.example.com:app.git",
		"file:///srv/git/app.git",
		"/srv/git/app.git",
		"app.git",
		"",
		"https://",
		"file://",
		"https://-oProxyCommand=touch/r.git",
		"https://[-oProxyCommand=touch]/r.git",
		"https://host.example:-1/r.git",
		"https://host.example/r.git\n--upload-pack=touch /tmp/pwned",
		"https://ho\nst.example/r.git",
		"https://host.example/r.git\x00x",
		"https://gi\nt@host.example/r.git",
	} {
		if pattern.MatchString(u) {
			t.Errorf("the pattern accepts %q", u)
		}
	}
}

func TestFresh(t *testing.T) {
	r := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed}
	if !r.Fresh("h1", "p1") || !r.Fresh("h1", "p2") || r.Fresh("h2", "p1") {
		t.Error("a result with the scope Head must depend only on the head")
	}
	r = &CheckResult{Commit: "h1", Scope: ScopeParent, ParentCommit: "p1", State: Passed}
	if !r.Fresh("h1", "p1") || r.Fresh("h1", "p2") || r.Fresh("h2", "p1") {
		t.Error("a result with the scope Parent must depend on both heads")
	}
	r = &CheckResult{Commit: "h1", Scope: ScopeChange, MergeBase: "b1", State: Passed}
	if !r.Fresh("h1", "p1") || !r.Fresh("h1", "p2") || r.Fresh("h2", "p1") {
		t.Error("a result with the scope Change must depend only on the head outside a landing")
	}
	for _, scope := range []string{"", "Parents", "head"} {
		if r := (&CheckResult{Commit: "h1", Scope: scope, State: Passed}); r.Fresh("h1", "p1") {
			t.Errorf("a result with the scope %q, which Fresh doesn't know, must be for no heads", scope)
		}
	}
	var missing *CheckResult
	if missing.Fresh("h1", "p1") || missing.Final() {
		t.Error("a missing result is never fresh or final")
	}
}

func TestEqual(t *testing.T) {
	r := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}, Notes: map[string]string{"runs": "1"}}
	same := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}, Notes: map[string]string{"runs": "1"}}
	if !r.Equal(same) {
		t.Error("results with the same fields aren't equal")
	}
	for _, edit := range []func(*CheckResult){
		func(o *CheckResult) { o.Commit = "h2" },
		func(o *CheckResult) { o.Scope = ScopeParent },
		func(o *CheckResult) { o.ParentCommit = "p1" },
		func(o *CheckResult) { o.MergeBase = "b1" },
		func(o *CheckResult) { o.State = Failed },
		func(o *CheckResult) { o.Message = "fine" },
		func(o *CheckResult) { o.Outputs = map[string]string{"level": "high"} },
		func(o *CheckResult) { o.Outputs = nil },
		func(o *CheckResult) { o.Notes = map[string]string{"runs": "2"} },
		func(o *CheckResult) { o.Notes = nil },
		func(o *CheckResult) { o.Pod = "gotest-1" },
		func(o *CheckResult) { o.Fix = "f1" },
		func(o *CheckResult) { o.FilesOnly = true },
	} {
		o := *same
		edit(&o)
		if r.Equal(&o) || o.Equal(r) {
			t.Errorf("%+v equals %+v", r, o)
		}
	}
	if r.Equal(nil) {
		t.Error("a result equals nil")
	}
	var missing *CheckResult
	if !missing.Equal(nil) {
		t.Error("nil results aren't equal")
	}
	empty := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Outputs: map[string]string{}, Notes: map[string]string{}}
	if !empty.Equal(&CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed}) {
		t.Error("empty outputs and notes don't equal none, but they look the same after a status write")
	}
}

// The schema that OpenAPISchema returns replaces the one that kube would
// generate from CheckResult's fields, so it must name each of them.
func TestCheckResultSchemaFields(t *testing.T) {
	s := CheckResult{}.OpenAPISchema()
	props := s["properties"].(map[string]any)
	var required []string
	typ := reflect.TypeFor[CheckResult]()
	for i := range typ.NumField() {
		name, opts, _ := strings.Cut(typ.Field(i).Tag.Get("json"), ",")
		if _, ok := props[name]; !ok {
			t.Errorf("the schema has no property %s", name)
		}
		if opts != "omitempty" {
			required = append(required, name)
		}
	}
	if len(props) != typ.NumField() {
		t.Errorf("the schema has %d properties, but CheckResult has %d fields", len(props), typ.NumField())
	}
	if got := s["required"].([]string); !slices.Equal(got, required) {
		t.Errorf("the schema requires %v, want %v", got, required)
	}
}

// The API server must accept every result that the results controller
// writes, so the schema's rules accept a combination of scope, parent
// commit, and merge base exactly when Validate does.
func TestCheckResultSchemaRules(t *testing.T) {
	env, err := cel.NewEnv(cel.Variable("self", cel.MapType(cel.StringType, cel.DynType)))
	if err != nil {
		t.Fatal(err)
	}
	type rule struct {
		prg     cel.Program
		message string
	}
	var rules []rule
	validations := CheckResult{}.OpenAPISchema()["x-kubernetes-validations"].([]any)
	for _, r := range validations {
		r := r.(map[string]any)
		ast, iss := env.Compile(r["rule"].(string))
		if iss.Err() != nil {
			t.Fatalf("compiling %q: %v", r["rule"], iss.Err())
		}
		prg, err := env.Program(ast)
		if err != nil {
			t.Fatal(err)
		}
		rules = append(rules, rule{prg, r["message"].(string)})
	}
	for _, scope := range []string{ScopeHead, ScopeParent, ScopeChange} {
		for _, parent := range []string{"", "p1"} {
			for _, base := range []string{"", "b1"} {
				res := CheckResult{Commit: "h1", Scope: scope, ParentCommit: parent, MergeBase: base, State: Passed}
				b, err := json.Marshal(res)
				if err != nil {
					t.Fatal(err)
				}
				var self map[string]any
				if err := json.Unmarshal(b, &self); err != nil {
					t.Fatal(err)
				}
				var rejected []string
				for _, r := range rules {
					out, _, err := r.prg.Eval(map[string]any{"self": self})
					if err != nil {
						t.Fatalf("%s: %v", b, err)
					}
					if out != types.True {
						rejected = append(rejected, r.message)
					}
				}
				verr := res.Validate()
				switch {
				case verr == nil && len(rejected) > 0:
					t.Errorf("Validate accepts %s, but the schema rejects it: %v", b, rejected)
				case verr != nil && len(rejected) == 0:
					t.Errorf("Validate rejects %s (%v), but the schema accepts it", b, verr)
				case verr != nil && !slices.Contains(rejected, verr.Error()):
					t.Errorf("Validate rejects %s with %q, and the schema with %v", b, verr, rejected)
				}
			}
		}
	}
}

// TestMergeStateEnum checks that status.state's enum lists every merge
// state and nothing else, so that the CRD accepts each state that the merge
// controller sets.
func TestMergeStateEnum(t *testing.T) {
	file, err := parser.ParseFile(token.NewFileSet(), "types.go", nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	var states []string
	for _, decl := range file.Decls {
		if d, ok := decl.(*ast.GenDecl); ok && d.Tok == token.CONST {
			for _, spec := range d.Specs {
				v := spec.(*ast.ValueSpec)
				if typ, ok := v.Type.(*ast.Ident); !ok || typ.Name != "MergeState" {
					continue
				}
				for _, value := range v.Values {
					s, err := strconv.Unquote(value.(*ast.BasicLit).Value)
					if err != nil {
						t.Fatal(err)
					}
					states = append(states, s)
				}
			}
		}
	}
	f, _ := reflect.TypeFor[BranchStatus]().FieldByName("State")
	var enum []string
	for opt := range strings.SplitSeq(f.Tag.Get("kube"), ",") {
		if values, ok := strings.CutPrefix(opt, "enum="); ok {
			enum = strings.Split(values, "|")
		}
	}
	slices.Sort(states)
	slices.Sort(enum)
	if len(states) == 0 || !slices.Equal(enum, states) {
		t.Errorf("status.state's enum is %v, want the MergeState constants %v", enum, states)
	}
}

func TestChecksMapIsAtomic(t *testing.T) {
	f, _ := reflect.TypeFor[BranchStatus]().FieldByName("Checks")
	if got := f.Tag.Get("kube"); got != "mapType=atomic" {
		t.Errorf("status.checks has kube tag %q; it must be an atomic map, so that the results controller owns every entry and can remove any of them", got)
	}
}

func TestMergePolicyDefaults(t *testing.T) {
	var p *MergePolicy
	if p.MaxCommits() != 5 || p.MaxRuns() != 10 || p.Check("gofmt") != nil {
		t.Error("a nil policy has the default limits and no checks")
	}
	zero := int32(0)
	p = &MergePolicy{Checks: []CheckPolicy{{Name: "gofmt", MayPush: true}}, MaxAutomatedCommits: &zero, MaxAgentRuns: &zero}
	if p.MaxCommits() != 0 || p.MaxRuns() != 0 {
		t.Errorf("MaxCommits = %d and MaxRuns = %d, want explicit 0s", p.MaxCommits(), p.MaxRuns())
	}
	if c := p.Check("gofmt"); c == nil || !c.MayPush {
		t.Errorf("Check(gofmt) = %+v", c)
	}
}

// kinds are the kinds that git-k8s defines. Their names make up the names
// of their CustomResourceDefinitions, which can't change once objects
// exist, so each kind's tag gives its plural and singular instead of
// leaving them to kube. Flux's source-controller defines a GitRepository
// kind with the plural gitrepositories and the short name gitrepo, so
// git-k8s doesn't use those names.
var kinds = []struct {
	typ                               reflect.Type
	kind, plural, singular, shortName string
}{
	{reflect.TypeFor[Repository](), "Repository", "repositories", "repository", "repo"},
	{reflect.TypeFor[Branch](), "Branch", "branches", "branch", "branch"},
}

// tagOptions splits a kube struct tag into its options.
func tagOptions(tag string) map[string]string {
	opts := map[string]string{}
	for opt := range strings.SplitSeq(tag, ",") {
		name, value, _ := strings.Cut(opt, "=")
		opts[name] = value
	}
	return opts
}

// TestKindNames checks each kind's names, and that every view type in the
// module, and every example of one in its docs, names a kind with its
// plural. The kind e2e test checks the names of the CustomResourceDefinitions
// that the core program installs.
func TestKindNames(t *testing.T) {
	plurals := map[string]string{}
	for _, k := range kinds {
		plurals[k.kind] = k.plural
		f, _ := k.typ.FieldByName("Object")
		tag := f.Tag.Get("kube")
		opts := tagOptions(tag)
		if cmp.Or(opts["kind"], k.typ.Name()) != k.kind || opts["plural"] != k.plural || opts["singular"] != k.singular {
			t.Errorf("%s has kube tag %q, want the kind %s with the plural %s and the singular %s", k.typ.Name(), tag, k.kind, k.plural, k.singular)
		}
		if opts["group"]+"/"+opts["version"] != APIVersion || opts["shortName"] != k.shortName || opts["category"] != "git-k8s" {
			t.Errorf("%s has kube tag %q, want %s with the short name %s in the category git-k8s", k.typ.Name(), tag, APIVersion, k.shortName)
		}
	}
	viewTag := regexp.MustCompile(`kube:"(apiVersion=` + regexp.QuoteMeta(Group) + `/[^"]*)"`)
	views := 0
	scan := func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return err
		}
		if ext := filepath.Ext(path); ext != ".go" && ext != ".md" {
			return nil
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		for _, m := range viewTag.FindAllSubmatch(src, -1) {
			views++
			opts := tagOptions(string(m[1]))
			if plural, ok := plurals[opts["kind"]]; !ok || opts["plural"] != plural || opts["apiVersion"] != APIVersion || opts["scope"] != "Namespaced" {
				t.Errorf("%s: view tag %q doesn't name a kind at %s with its plural", path, m[1], APIVersion)
			}
		}
		return nil
	}
	if err := filepath.WalkDir(".", scan); err != nil {
		t.Fatal(err)
	}
	if views == 0 {
		t.Error("found no view types")
	}
}

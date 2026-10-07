package gitk8s

import (
	"encoding/json"
	"reflect"
	"regexp"
	"slices"
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
	field, _ := reflect.TypeFor[GitRepositorySpec]().FieldByName("URL")
	pattern := regexp.MustCompile(field.Tag.Get("pattern"))
	for _, u := range []string{
		"https://git.example.com/app.git",
		"http://172.18.0.1:18418/app.git",
		"https://[2001:db8::1]/app.git",
		"git://git.example.com/app.git",
		"ssh://git@git.example.com:2222/app.git",
		"ssh://git@[::1]:2222/app.git",
		"ssh://example.com/~/app.git",
		"https://git-k8s@git.example.com/app.git",
		"git@github.com:imjasonh/playground.git",
		"git@[172.18.0.1:2222]:app.git",
		"git@[::1]:app.git",
	} {
		if !pattern.MatchString(u) {
			t.Errorf("the pattern rejects %q", u)
		}
	}
	for _, u := range []string{
		"--upload-pack=touch /tmp/pwned",
		"-oProxyCommand=touch /tmp/pwned",
		"-git@git.example.com:app.git",
		"git@-oProxyCommand=touch:app.git",
		"ssh://-oProxyCommand=touch/app.git",
		"ssh://git@-oProxyCommand=touch/app.git",
		"ssh://-git@git.example.com/app.git",
		"ext::sh -c touch% /tmp/pwned",
		"fd::3",
		"s3://bucket/app.git",
		"HTTPS://git.example.com/app.git",
		"git.example.com:app.git",
		"file:///srv/git/app.git",
		"/srv/git/app.git",
		"app.git",
		"",
		"ssh://%2doProxyCommand=touch%20/tmp/pwned/r.git",
		"ssh://%2DoProxyCommand=touch/r.git",
		"ssh://git@%2doProxyCommand=touch/r.git",
		"ssh://%2dgit@host.example/r.git",
		"ssh://u%40h@%2doProxyCommand=touch/r.git",
		"ssh://[-oProxyCommand=touch]/r.git",
		"ssh://[-oProxyCommand=touch]:22/r.git",
		"ssh://git@[-oProxyCommand=touch]/r.git",
		"git@[-oProxyCommand=touch]:r.git",
		"[-x@host.example]:r.git",
		"git@%2doProxyCommand=touch:r.git",
		"ssh://host.example:-oProxyCommand=touch/r.git",
		"ssh://host.example:%2doProxyCommand=touch/r.git",
		"ssh://\u2010oProxyCommand=touch/r.git",
		"https://",
		"file://",
		"https://host.example/r.git\n--upload-pack=touch /tmp/pwned",
		"https://ho\nst.example/r.git",
		"https://host.example/r.git\x00x",
		"ssh://[-x]@host.example/r.git",
		"[-x@host.example:22]:r.git",
		"git@host.example:-oProxyCommand=touch",
		"git@host.example:",
		"ssh://gi\nt@host.example/r.git",
		"gi\nt@host.example:r.git",
		"git@[host.example:-0]:r.git",
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
	r := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}}
	same := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}}
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
	empty := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed, Outputs: map[string]string{}}
	if !empty.Equal(&CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed}) {
		t.Error("empty outputs don't equal no outputs, but they look the same after a status write")
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

func TestChecksMapIsAtomic(t *testing.T) {
	f, _ := reflect.TypeFor[GitBranchStatus]().FieldByName("Checks")
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

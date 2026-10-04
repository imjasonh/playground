package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"maps"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

const (
	depsBranch = "deps/go/example.com/greet"
	testOutput = "go test failed in Pod gotest-1: --- FAIL: TestGreet\n    greet_test.go:9: got \"hello\", want \"hello, world\"\nFAIL"
	reasoning  = "Hello takes a name in v1.1.0, so Greet passes one."
)

// fixture is a branch that updates a module on a git server, and the gotest
// check's result on it.
type fixture struct {
	t    *testing.T
	srv  *gittest.Server
	work *gittest.Work
	b    *Branch
	test *gitk8s.CheckResult
	cfg  *checks.Config
}

func newFixture(t *testing.T, branch string) *fixture {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("go.mod", "module example.com/app\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n")
	w.Write("app.go", "package app\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch(branch, main)
	w.Write("go.mod", "module example.com/app\n\ngo 1.24\n\nrequire example.com/greet v1.1.0\n")
	head := w.Commit("Update example.com/greet to v1.1.0\n\nGit-K8s-Deps: go example.com/greet v1.1.0")
	w.Push(branch)

	b := &Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", branch), nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: branch, Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gotest"}, {Name: "deps", MayPush: true}}},
	}
	return &fixture{
		t: t, srv: srv, work: w, b: b,
		test: &gitk8s.CheckResult{Commit: head, State: gitk8s.Failed, Message: testOutput},
		cfg:  &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}},
	}
}

func (f *fixture) reconcile() *kube.Recorder {
	f.t.Helper()
	repo, secret := f.srv.Repository("app")
	tr := &testResult{Object: kube.Meta(f.b.Name, nil)}
	tr.Namespace = f.b.Namespace
	tr.Status.Checks.Gotest = f.test
	ctx, rec := kube.Fake(f.t.Context(), f.b, repo, secret, tr)
	if err := checks.NewReconciler[Branch](check, f.cfg).Reconcile(ctx, f.b); err != nil {
		f.t.Fatal(err)
	}
	return rec
}

func (f *fixture) result() *gitk8s.CheckResult { return f.b.Status.Checks.Result }

// replaceAgent makes runAgent call fake for the rest of the test.
func replaceAgent(t *testing.T, fake func(context.Context, *checks.Input, agent.Task) (checks.Verdict, *agent.Result)) {
	old := runAgent
	t.Cleanup(func() { runAgent = old })
	runAgent = fake
}

// noAgent fails the test if the check runs an agent.
func noAgent(t *testing.T) {
	replaceAgent(t, func(context.Context, *checks.Input, agent.Task) (checks.Verdict, *agent.Result) {
		t.Error("the check ran an agent")
		return checks.Verdict{State: gitk8s.Running}, nil
	})
}

// agentThat makes the agent answer verdict after changing files, as
// Runner.Run reports a finished run, and returns the task that the agent
// gets.
func (f *fixture) agentThat(verdict string, files ...agent.File) *agent.Task {
	task := &agent.Task{}
	replaceAgent(f.t, func(ctx context.Context, in *checks.Input, t agent.Task) (checks.Verdict, *agent.Result) {
		*task = t
		res := &agent.Result{Verdict: verdict, Summary: "updated Greet", Reasoning: reasoning, Files: files}
		v := checks.Verdict{State: gitk8s.Passed, Message: reasoning, Outputs: map[string]string{"summary": res.Summary, "runs": "1"}}
		if verdict == agent.Fail {
			v.State = gitk8s.Failed
		}
		if len(files) > 0 {
			v.Fix = f.commit(ctx, in, files)
		}
		return v, res
	})
	return task
}

// commit makes the fix commit that the agent package makes for files.
func (f *fixture) commit(ctx context.Context, in *checks.Input, files []agent.File) string {
	f.t.Helper()
	repo, err := in.Repo(ctx)
	if err != nil {
		f.t.Fatal(err)
	}
	head, err := repo.Commit(ctx, in.Spec.Head)
	if err != nil {
		f.t.Fatal(err)
	}
	tree, err := agent.ApplyFiles(ctx, repo, head.Tree, files)
	if err != nil {
		f.t.Fatal(err)
	}
	msg := "Apply changes from the deps agent\n\n" + git.FixerTrailer + ": deps\n" + git.AgentTrailer + ": deps\n"
	fix, err := repo.CommitTree(ctx, tree, []string{in.Spec.Head}, msg, in.Identity, head.Time)
	if err != nil {
		f.t.Fatal(err)
	}
	return fix
}

func TestPassesOtherBranches(t *testing.T) {
	noAgent(t)
	f := newFixture(t, "c/x")
	f.b.Status.Checks.Result = &gitk8s.CheckResult{Commit: "0123abcd", State: gitk8s.Failed, Outputs: map[string]string{"runs": "2"}}
	rec := f.reconcile()
	if res := f.result(); res.State != gitk8s.Passed || res.Message != "c/x isn't a dependency branch" || len(res.Outputs) != 1 || res.Outputs["runs"] != "2" || len(kube.Owned[agent.Pod](rec)) != 0 {
		t.Errorf("result = %+v, want Passed with the count of agent runs and without a Pod", res)
	}
}

func TestNeedsAValidPrefix(t *testing.T) {
	defer func(r *agent.Runner) { runner = r }(runner)
	runner = &agent.Runner{Name: "deps"}
	t.Cleanup(func() { prefix = "deps/" })
	if err := new(branchPrefix).Set(string(prefix)); err != nil {
		t.Errorf("the default -prefix, %q, isn't valid: %v", prefix, err)
	}
	parse := func(value string) error {
		fs := flag.NewFlagSet("check-deps", flag.ContinueOnError)
		fs.SetOutput(io.Discard)
		addFlags(fs)
		return fs.Parse([]string{"-prefix=" + value})
	}
	for _, p := range []string{"", "deps", "/", "deps//", "-deps/", "deps..x/", ".deps/", "deps.lock/", "de ps/"} {
		want := fmt.Sprintf("invalid value %q for flag -prefix: it must be a branch-name prefix that ends with /, such as deps/", p)
		if err := parse(p); err == nil || err.Error() != want {
			t.Errorf("parsing -prefix=%q = %v, want %s", p, err, want)
		}
		if prefix != "deps/" {
			t.Fatalf("parsing -prefix=%q set the prefix to %q", p, prefix)
		}
	}
	if err := parse("updates/"); err != nil {
		t.Fatalf("parsing -prefix=updates/ = %v", err)
	}
	noAgent(t)
	f := newFixture(t, depsBranch)
	rec := f.reconcile()
	if res := f.result(); res.State != gitk8s.Passed || res.Message != depsBranch+" isn't a dependency branch" || len(kube.Owned[agent.Pod](rec)) != 0 {
		t.Errorf("with -prefix=updates/, result = %+v, want Passed without a Pod because %s isn't a dependency branch", res, depsBranch)
	}
}

func TestFollowsTheTests(t *testing.T) {
	waiting := "waiting for the gotest check"
	for _, tc := range []struct {
		name string
		// testState is the gotest check's state, or "" for no result.
		testState string
		older     bool
		readOnly  bool
		noTests   bool
		state     string
		message   string
	}{
		{name: "no result", state: gitk8s.Running, message: waiting},
		{name: "running", testState: gitk8s.Running, state: gitk8s.Running, message: waiting},
		{name: "an error", testState: gitk8s.Error, state: gitk8s.Running, message: waiting},
		{name: "an older head", testState: gitk8s.Failed, older: true, state: gitk8s.Running, message: waiting},
		{name: "passed", testState: gitk8s.Passed, state: gitk8s.Passed, message: "go test passed"},
		{
			name: "failed without mayPush", testState: gitk8s.Failed, readOnly: true,
			state: gitk8s.Failed, message: "go test failed, and the policy doesn't let the deps check push a fix",
		},
		{
			name: "no gotest check", testState: gitk8s.Failed, noTests: true,
			state: gitk8s.Passed, message: "the merge policy doesn't run the gotest check",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			noAgent(t)
			f := newFixture(t, depsBranch)
			f.test = nil
			if tc.testState != "" {
				f.test = &gitk8s.CheckResult{Commit: f.b.Spec.Head, State: tc.testState, Message: testOutput}
				if tc.older {
					f.test.Commit = "0123abcd"
				}
			}
			f.b.Spec.Merge.Checks[1].MayPush = !tc.readOnly
			if tc.noTests {
				f.b.Spec.Merge.Checks = f.b.Spec.Merge.Checks[1:]
			}
			f.b.Status.Checks.Result = &gitk8s.CheckResult{Commit: "0123abcd", State: gitk8s.Fixed, Outputs: map[string]string{"runs": "3", "fix": "4567cdef"}}
			rec := f.reconcile()
			res := f.result()
			if res.State != tc.state || res.Message != tc.message || len(kube.Owned[agent.Pod](rec)) != 0 {
				t.Fatalf("result = %+v, want %s with %q and no Pod", res, tc.state, tc.message)
			}
			if len(res.Outputs) != 1 || res.Outputs["runs"] != "3" {
				t.Errorf("outputs = %v, want only the count of agent runs", res.Outputs)
			}
		})
	}
}

func TestStopsAtTheCommitLimit(t *testing.T) {
	noAgent(t)
	f := newFixture(t, depsBranch)
	for i := range 2 {
		f.work.Write("app.go", "package app\n\n// "+string(rune('a'+i))+"\n")
		f.b.Spec.Head = f.work.Commit("Apply changes from the deps agent\n\nGit-K8s-Fixer: deps")
	}
	f.work.Push(depsBranch)
	f.test.Commit = f.b.Spec.Head
	limit := int32(2)
	f.b.Spec.Merge.MaxAutomatedCommits = &limit
	f.reconcile()
	want := "go test failed, and the branch used all 2 automated commits that maxAutomatedCommits allows, so a person needs to fix it"
	if res := f.result(); res.State != gitk8s.Failed || res.Message != want {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
}

func TestStartsAnAgentThatCanEdit(t *testing.T) {
	defer func(r *agent.Runner) { runner = r }(runner)
	runner = &agent.Runner{Name: "deps", Image: "agent-runner", GitImage: "git", Backend: "fake", Model: "composer-2.5", Secret: "cursor-api-key", Timeout: time.Minute}
	f := newFixture(t, depsBranch)
	rec := f.reconcile()
	pods := kube.Owned[agent.Pod](rec)
	if res := f.result(); res.State != gitk8s.Running || len(pods) != 1 || res.Outputs["pod"] != pods[0].Name {
		t.Fatalf("result = %+v and %d Pods, want Running with one Pod", res, len(pods))
	}
	var task struct {
		Instructions string `json:"instructions"`
		Edit         bool   `json:"edit"`
	}
	if err := json.Unmarshal([]byte(pods[0].Spec.InitContainers[1].Env[0].Value), &task); err != nil {
		t.Fatal(err)
	}
	if !task.Edit || task.Instructions != instructions(testOutput) {
		t.Errorf("the agent's task = %+v, want edits and the test output", task)
	}
}

func TestPushesTheAgentsFix(t *testing.T) {
	f := newFixture(t, depsBranch)
	task := f.agentThat(agent.Pass, agent.File{Path: "app.go", Mode: "100644", Content: []byte("package app\n\n// fixed\n")})
	f.reconcile()
	res := f.result()
	fix := res.Outputs["fix"]
	if res.State != gitk8s.Fixed || fix == "" || res.Message != reasoning+"; pushed "+gitk8s.Short(fix) || res.Outputs["runs"] != "1" {
		t.Fatalf("result = %+v, want Fixed with the agent's fix", res)
	}
	if got := f.work.Fetch(depsBranch); got != fix {
		t.Errorf("%s = %s, want the fix %s", depsBranch, got, fix)
	}
	if !task.Edit || task.Instructions != instructions(testOutput) {
		t.Errorf("the agent's task = %+v, want edits and the test output", task)
	}
}

func TestDoesntPushWhatDoesntFixTheTests(t *testing.T) {
	code := agent.File{Path: "app.go", Mode: "100644", Content: []byte("package app\n\n// fixed\n")}
	for _, tc := range []struct {
		name    string
		verdict string
		files   []agent.File
		message string
	}{{
		name: "the agent fails", verdict: agent.Fail, files: []agent.File{code},
		message: "the agent couldn't fix the tests: " + reasoning,
	}, {
		name: "the agent changes go.mod", verdict: agent.Pass,
		files:   []agent.File{code, {Path: "go.mod", Mode: "100644", Content: []byte("module example.com/app\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n")}},
		message: "the agent changed a go.mod file, so a person needs to finish the update: " + reasoning,
	}, {
		name: "the agent changes a nested go.sum", verdict: agent.Pass,
		files:   []agent.File{{Path: "tools/go.sum", Deleted: true}},
		message: "the agent changed a go.sum file, so a person needs to finish the update: " + reasoning,
	}, {
		name: "the agent adds go.work", verdict: agent.Pass,
		files:   []agent.File{code, {Path: "go.work", Mode: "100644", Content: []byte("go 1.24\n\nuse .\n\nreplace example.com/greet => ./greet\n")}},
		message: "the agent changed a go.work file, so a person needs to finish the update: " + reasoning,
	}, {
		name: "the agent changes a nested go.work.sum", verdict: agent.Pass,
		files:   []agent.File{code, {Path: "tools/go.work.sum", Mode: "100644", Content: []byte("example.com/greet v1.0.0 h1:x=\n")}},
		message: "the agent changed a go.work.sum file, so a person needs to finish the update: " + reasoning,
	}, {
		name: "the agent changes nothing", verdict: agent.Pass,
		message: "the agent didn't change any files: " + reasoning,
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, depsBranch)
			head := f.b.Spec.Head
			f.agentThat(tc.verdict, tc.files...)
			f.reconcile()
			if res := f.result(); res.State != gitk8s.Failed || res.Message != tc.message || res.Outputs["fix"] != "" {
				t.Errorf("result = %+v, want Failed with %q and no fix", res, tc.message)
			}
			if got := f.work.Fetch(depsBranch); got != head {
				t.Errorf("%s = %s, want it to stay at %s", depsBranch, got, head)
			}
		})
	}
}

func TestReportsWhatAFailedRunUsed(t *testing.T) {
	f := newFixture(t, depsBranch)
	failed := checks.Verdict{
		State:   gitk8s.Failed,
		Message: "the agent failed in Pod deps-0123abcd: the Cursor API returned 429",
		Outputs: map[string]string{
			"runs": "1", "pod": "deps-0123abcd", "model": "composer-2.5", "inputTokens": "1200", "outputTokens": "300",
			"cacheReadTokens": "0", "cacheWriteTokens": "0", "costCents": "4",
		},
	}
	replaceAgent(t, func(context.Context, *checks.Input, agent.Task) (checks.Verdict, *agent.Result) {
		return failed, nil
	})
	f.reconcile()
	if res := f.result(); res.State != gitk8s.Failed || res.Message != failed.Message || !maps.Equal(res.Outputs, failed.Outputs) {
		t.Errorf("result = %+v, want the runner's verdict with what the run used", res)
	}
}

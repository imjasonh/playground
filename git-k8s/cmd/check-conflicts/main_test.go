package main

import (
	"cmp"
	"context"
	"encoding/json"
	"fmt"
	"maps"
	"os"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

const downstream = "refs/git-k8s/downstream/heads/"

var (
	conflictingA   = map[string]string{"a.txt": "one\nmain\nthree\n"}
	conflictingSum = map[string]string{"go.sum": "a v1\nb v1\n"}
)

// setup pushes main and c/x, which both start from base, a commit with
// a.txt and go.sum. main changes the files in mainFiles, and c/x those in
// branchFiles. It returns c/x's view, whose policy lets the conflicts
// check push.
func setup(t *testing.T, srv *gittest.Server, mainFiles, branchFiles map[string]string) (b *Branch, w *gittest.Work, base string) {
	w = srv.NewWork(t, "app")
	w.Write("a.txt", "one\ntwo\nthree\n")
	w.Write("go.sum", "a v1\n")
	base = w.Commit("base")
	parent := commit(w, "main edit", mainFiles)
	w.Push("main")
	w.Branch("c/x", base)
	head := commit(w, "branch edit", branchFiles)
	w.Push("c/x")
	b = &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: parent,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "conflicts", MayPush: true}}},
	}
	return b, w, base
}

func commit(w *gittest.Work, message string, files map[string]string) string {
	for path, content := range files {
		w.Write(path, content)
	}
	return w.Commit(message)
}

// diverge pushes a commit on from that changes files to the ref that holds
// the external repository's head of branch. It returns the commit, and the
// divergence of the GitBranch called name.
func diverge(w *gittest.Work, name, branch, from string, files map[string]string) (string, *observed) {
	w.Branch("external", from)
	e := commit(w, "external edit", files)
	w.PushRef(downstream + branch)
	o := &observed{Object: kube.Meta(name, nil)}
	o.Namespace = "default"
	o.Status.Diverged = &gitk8s.Divergence{Commit: e, Ref: downstream + branch}
	return e, o
}

// syncedAt pushes synced to the ref that holds the head where branch last
// synced, and records it as o's base.
func syncedAt(w *gittest.Work, o *observed, branch, synced string) {
	w.Branch("synced", synced)
	w.PushRef(syncedPrefix + branch)
	o.Status.Diverged.Base = synced
}

// files lists the files at commit.
func files(w *gittest.Work, commit string) string {
	return w.Git("ls-tree", "--name-only", "--end-of-options", commit)
}

// rules give main a policy with the conflicts check and every other branch
// the parent main.
var rules = []gitk8s.BranchRule{
	{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "conflicts", MayPush: true}}}},
	{Match: "**", Parent: "main"},
}

// reconcile runs the controller on b with the repository app, which has
// rules, and the objects in world.
func reconcile(t *testing.T, srv *gittest.Server, b *Branch, rules []gitk8s.BranchRule, world ...any) (*kube.Recorder, error) {
	t.Helper()
	repo, secret := srv.Repository("app", rules...)
	ctx, rec := kube.Fake(t.Context(), b, append([]any{repo, secret}, world...)...)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return rec, newReconciler(cfg).Reconcile(ctx, b)
}

// withAgent runs agents with the fake backend for the rest of the test.
func withAgent(t *testing.T) {
	r := runner
	t.Cleanup(func() { runner = r })
	runner = &agent.Runner{Name: "conflicts", Image: "agent-runner", GitImage: "git", Backend: "fake", Model: "composer-2.5", Secret: "cursor-api-key", Timeout: time.Minute}
}

func withUnion(t *testing.T, p ...string) {
	u := union
	t.Cleanup(func() { union = u })
	union = p
}

// withJobs runs the agent's jobs with fn for the rest of the test, and
// returns the jobs that the check ran.
func withJobs(t *testing.T, fn func(job *agent.Job, st *agent.JobState) agent.JobStatus) *[]*agent.Job {
	withAgent(t)
	r := runJob
	t.Cleanup(func() { runJob = r })
	var jobs []*agent.Job
	runJob = func(_ context.Context, job *agent.Job, st *agent.JobState) agent.JobStatus {
		jobs = append(jobs, job)
		return fn(job, st)
	}
	return &jobs
}

// finish finishes each run with res, as RunJob does once it fetches the
// agent's result, with the tree of the merge that the agent's Pod makes in
// w. Like RunJob, it reports a run whose JobState is done as done without
// its result.
func finish(t *testing.T, w *gittest.Work, res *agent.Result) func(*agent.Job, *agent.JobState) agent.JobStatus {
	return func(job *agent.Job, st *agent.JobState) agent.JobStatus {
		if st.Done {
			return agent.JobStatus{Done: true, Message: "the run in Pod " + st.Pod + " already finished"}
		}
		st.Runs, st.Pod, st.Attempt, st.Done = st.Runs+1, "conflicts-app-c-x-1", 1, true
		res := *res
		res.MergeTree = mergeTree(t, w, job)
		return agent.JobStatus{Done: true, Message: cmp.Or(res.Reasoning, res.Summary), Result: &res}
	}
}

// mergeTree is the tree of the merge that the agent's Pod makes for job,
// in w, which holds the job's commits.
func mergeTree(t *testing.T, w *gittest.Work, job *agent.Job) string {
	t.Helper()
	repo, err := (&git.Git{}).Open(t.Context(), w.Dir+"/.git")
	if err != nil {
		t.Fatal(err)
	}
	c := job.Checkout
	tree, _, err := repo.Merge(t.Context(), c.Head, c.Merge.Commit, git.MergeOptions{Base: c.Base, Union: c.Union})
	if err != nil {
		t.Fatal(err)
	}
	return tree
}

// podTask is what a Pod's AGENT_TASK says about the agent's task.
type podTask struct {
	Instructions string   `json:"instructions"`
	Edit         bool     `json:"edit"`
	Tools        []string `json:"tools"`
	Base         string   `json:"base"`
	MergeName    string   `json:"mergeName"`
	MergeHead    string   `json:"mergeHead"`
}

func agentTask(t *testing.T, p *agent.Pod) podTask {
	t.Helper()
	var task podTask
	if err := json.Unmarshal([]byte(p.Spec.InitContainers[1].Env[0].Value), &task); err != nil {
		t.Fatal(err)
	}
	return task
}

func prepareEnv(p *agent.Pod, name string) string {
	for _, e := range p.Spec.InitContainers[0].Env {
		if e.Name == name {
			return e.Value
		}
	}
	return ""
}

func TestPassesWithoutAMergeToResolve(t *testing.T) {
	for _, tc := range []struct {
		name, want string
		move       func(w *gittest.Work, b *Branch)
	}{{
		name: "the branch contains main",
		want: "contains main at ",
		move: func(w *gittest.Work, b *Branch) {
			w.Branch("c/x", b.Spec.ParentHead)
			b.Spec.Head = commit(w, "after main", map[string]string{"c.txt": "c\n"})
			w.Push("c/x")
		},
	}, {
		name: "main contains the branch",
		want: "main at ",
		move: func(w *gittest.Work, b *Branch) {
			w.Branch("main", b.Spec.Head)
			b.Spec.ParentHead = commit(w, "main moves past the branch", map[string]string{"c.txt": "c\n"})
			w.Push("main")
		},
	}, {
		name: "the merge has no conflicts",
		want: "merging main at ",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, _ := setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"c.txt": "branch\n"})
			if tc.move != nil {
				tc.move(w, b)
			}
			head := b.Spec.Head
			if _, err := reconcile(t, srv, b, rules); err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasPrefix(res.Message, tc.want) {
				t.Errorf("result = %+v, want Passed with a message that starts %q", res, tc.want)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestMergesUnionPaths(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, _ := setup(t, srv, conflictingSum, map[string]string{"go.sum": "a v1\nc v1\n"})
	head, parent := b.Spec.Head, b.Spec.ParentHead
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: "0123", State: gitk8s.Failed, Outputs: stateOutputs(&agent.JobState{Runs: 3})}
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	if res.State != gitk8s.Fixed || fix == "" || !strings.HasPrefix(res.Message, "merging main conflicts in go.sum, which git merged with its union driver; pushed ") {
		t.Fatalf("result = %+v, want Fixed with a pushed merge", res)
	}
	if res.Outputs["conflicts"] != "go.sum" || res.Outputs["merge"] != parent || readState(res.Outputs).Runs != 3 {
		t.Errorf("outputs = %v, want the conflicts, the merged commit, and the earlier runs", res.Outputs)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the merge %s", got, fix)
	}
	want := head + " " + parent + "\nMerge main into c/x\n\nGit merged these files with its union driver, which keeps the lines of both sides:\n\ngo.sum\n\n" + git.FixerTrailer + ": conflicts"
	if got := w.Git("log", "-1", "--format=%P%n%B", "--end-of-options", fix); got != want {
		t.Errorf("merge's parents and message =\n%s\nwant\n%s", got, want)
	}
	if got := w.Show(fix, "go.sum"); got != "a v1\nc v1\nb v1" {
		t.Errorf("go.sum = %q, want the lines of both sides", got)
	}

	b.Spec.Head = fix
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasPrefix(res.Message, "contains main at ") {
		t.Errorf("result after the merge = %+v, want Passed", res)
	}
}

func TestLeavesConflictsThatItCantResolve(t *testing.T) {
	// both commits files on top of main and of c/x.
	both := func(b *Branch, w *gittest.Work, mainFiles, branchFiles map[string]string) {
		w.Branch("main", b.Spec.ParentHead)
		b.Spec.ParentHead = commit(w, "main edit", mainFiles)
		w.Push("main")
		w.Branch("c/x", b.Spec.Head)
		b.Spec.Head = commit(w, "branch edit", branchFiles)
		w.Push("c/x")
	}
	for _, tc := range []struct {
		name  string
		agent bool
		edit  func(b *Branch, w *gittest.Work)
		state string
		want  string
	}{{
		name: "without an agent image",
		want: "merging main conflicts in a.txt; git can't resolve them, and the check runs no agent without -agent-image",
	}, {
		name:  "when the policy doesn't let it push",
		agent: true,
		edit:  func(b *Branch, _ *gittest.Work) { b.Spec.Merge.Checks[1].MayPush = false },
		want:  "merging main conflicts in a.txt; the policy doesn't let this check push a resolution, so it runs no agent",
	}, {
		name:  "when the branch has no automated commits left",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			b.Spec.Merge.MaxAutomatedCommits = new(int32(1))
			w.Write("b.txt", "fixed\n")
			w.Git("add", "-A")
			w.Git("commit", "--quiet", "-m", "Fix\n\n"+git.FixerTrailer+": gofmt")
			b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
			w.Push("c/x")
		},
		want: "merging main conflicts in a.txt; not running an agent because the branch already has 1 automated commits, the limit",
	}, {
		name:  "when the branch shares no history with main",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			w.Git("checkout", "--quiet", "--orphan", "unrelated")
			b.Spec.Head = commit(w, "unrelated", map[string]string{"a.txt": "unrelated\n"})
			w.Push("c/x")
		},
		want: "the branch shares no history with main, so git can't merge them",
	}, {
		name:  "when main deleted the file that conflicts",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			w.Branch("main", b.Spec.ParentHead+"~1")
			w.Git("rm", "--quiet", "--end-of-options", "a.txt")
			b.Spec.ParentHead = w.Commit("delete a.txt")
			w.Push("main")
		},
		want: "merging main conflicts on a.txt, which isn't a file on both sides, so the agent can't resolve it",
	}, {
		name:  "in a binary file",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			both(b, w, map[string]string{"b.bin": "\x00main\n"}, map[string]string{"b.bin": "\x00branch\n"})
		},
		want: "merging main conflicts on b.bin, which git can't mark with conflict markers, such as a binary file",
	}, {
		name:  "in a symbolic link",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			for _, side := range []struct {
				branch string
				head   *string
			}{{"main", &b.Spec.ParentHead}, {"c/x", &b.Spec.Head}} {
				w.Branch(side.branch, *side.head)
				// Work.Write writes only regular files, so this stages the
				// link and checks it out over the file.
				w.Write("b.link", side.branch+".txt")
				blob := w.Git("hash-object", "-w", "--end-of-options", "b.link")
				w.Git("update-index", "--add", "--cacheinfo", "120000,"+blob+",b.link")
				w.Git("checkout-index", "--force", "--end-of-options", "b.link")
				*side.head = w.Commit("link b.link to " + side.branch + ".txt")
				w.Push(side.branch)
			}
		},
		want: "merging main conflicts on b.link, which isn't a file on both sides, so the agent can't resolve it",
	}, {
		name:  "in a .cursorignore file",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			both(b, w, map[string]string{".cursorignore": "main\n"}, map[string]string{".cursorignore": "branch\n"})
		},
		want: "merging main conflicts on .cursorignore, which the agent can't see, because its work tree leaves out .cursorignore files",
	}, {
		name:  "when the branch and main have two merge bases",
		agent: true,
		edit: func(b *Branch, w *gittest.Work) {
			head, parent := b.Spec.Head, b.Spec.ParentHead
			w.Branch("c/x", head)
			w.Git("merge", "--quiet", "--no-edit", "-s", "ours", "--end-of-options", parent)
			b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
			w.Branch("main", parent)
			w.Git("merge", "--quiet", "--no-edit", "-s", "ours", "--end-of-options", head)
			b.Spec.ParentHead = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
			both(b, w, map[string]string{"a.txt": "one\nmain again\nthree\n"}, map[string]string{"a.txt": "one\nbranch again\nthree\n"})
		},
		want: "the branch and main have 2 merge bases, so their conflicts have no one base for the agent to compare",
	}, {
		name:  "when the branch used all its agent runs",
		agent: true,
		edit: func(b *Branch, _ *gittest.Work) {
			b.Status.Checks.Result = &gitk8s.CheckResult{Commit: "0123", State: gitk8s.Failed, Outputs: stateOutputs(&agent.JobState{Runs: 10})}
		},
		state: gitk8s.Running,
		want:  "merging main conflicts in a.txt; not starting the agent: the job used all 10 of its runs",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			if tc.agent {
				withAgent(t)
			}
			srv := gittest.NewServer(t, "")
			b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
			if tc.edit != nil {
				tc.edit(b, w)
			}
			head := b.Spec.Head
			rec, err := reconcile(t, srv, b, rules)
			if err != nil {
				t.Fatal(err)
			}
			if res, want := b.Status.Checks.Result, cmp.Or(tc.state, gitk8s.Failed); res.State != want || res.Message != tc.want {
				t.Errorf("result = %+v, want %s with %q", res, want, tc.want)
			}
			if pods := kube.Owned[agent.Pod](rec); len(pods) != 0 {
				t.Errorf("started %d agent Pods, want none", len(pods))
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestLeavesTheRunLimitsToRunJob(t *testing.T) {
	var got agent.JobState
	jobs := withJobs(t, func(_ *agent.Job, st *agent.JobState) agent.JobStatus {
		got = *st
		return agent.JobStatus{Message: "not starting the agent: the job used all 3 of its runs"}
	})
	srv := gittest.NewServer(t, "")
	b, _, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	three := int32(3)
	b.Spec.Merge.MaxAgentRuns = &three
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: "0123", State: gitk8s.Failed, Outputs: stateOutputs(&agent.JobState{Runs: 3})}
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	if len(*jobs) != 1 || (*jobs)[0].MaxRuns != 3 || got != (agent.JobState{Runs: 3}) {
		t.Fatalf("ran %d jobs, the last with the state %+v, want one with MaxRuns 3 for a state with 3 runs", len(*jobs), got)
	}
	res := b.Status.Checks.Result
	want := "merging main conflicts in a.txt; not starting the agent: the job used all 3 of its runs"
	if res.State != gitk8s.Running || res.Message != want || readState(res.Outputs).Runs != 3 {
		t.Errorf("result = %+v, want Running with %q and 3 runs", res, want)
	}
}

func TestStartsAnAgent(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "")
	b, _, base := setup(t, srv,
		map[string]string{"a.txt": "one\nmain\nthree\n", "go.sum": "a v1\nb v1\n"},
		map[string]string{"a.txt": "one\nbranch\nthree\n", "go.sum": "a v1\nc v1\n"})
	rec, err := reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	pods := kube.Owned[agent.Pod](rec)
	if res.State != gitk8s.Running || len(pods) != 1 {
		t.Fatalf("result = %+v and %d Pods, want Running with one Pod", res, len(pods))
	}
	want := stateOutputs(&agent.JobState{Runs: 1, Pod: pods[0].Name, Attempt: 1})
	maps.Copy(want, map[string]string{"conflicts": "a.txt,go.sum", "merge": b.Spec.ParentHead, "base": base, "union": "go.sum"})
	if !maps.Equal(res.Outputs, want) {
		t.Errorf("outputs = %v, want %v", res.Outputs, want)
	}
	task := agentTask(t, pods[0])
	if !task.Edit || task.Instructions != instructions || !slices.Equal(task.Tools, tools) || task.Base != base ||
		task.MergeName != "main" || task.MergeHead != b.Spec.ParentHead {
		t.Errorf("the agent's task = %+v, want a merge of main", task)
	}
	for name, want := range map[string]string{"MERGE_REF": "refs/heads/main", "MERGE_HEAD": b.Spec.ParentHead, "ATTRIBUTES": "go.sum merge=union\n"} {
		if got := prepareEnv(pods[0], name); got != want {
			t.Errorf("%s = %q, want %q", name, got, want)
		}
	}
}

func TestFollowsTheAgentWhileMainMoves(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	started := b.Spec.ParentHead
	rec, err := reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	pod := kube.Owned[agent.Pod](rec)[0].Name

	w.Branch("main", started)
	b.Spec.ParentHead = commit(w, "main moves", map[string]string{"d.txt": "d\n"})
	w.Push("main")
	rec, err = reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	pods := kube.Owned[agent.Pod](rec)
	if res.State != gitk8s.Running || len(pods) != 1 || pods[0].Name != pod {
		t.Fatalf("result = %+v and Pods %v, want Running with Pod %s", res, pods, pod)
	}
	if res.Outputs["merge"] != started || res.Outputs["conflicts"] != "a.txt" || res.Outputs["runs"] != "1" {
		t.Errorf("outputs = %v, want the run that merges main at %s", res.Outputs, started)
	}
}

func TestFollowsTheAgentWhileGitFails(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "pw")
	b, _, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	rec, err := reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	pod := kube.Owned[agent.Pod](rec)[0].Name

	repo, secret := srv.Repository("app", rules...)
	secret.Data["password"] = []byte("wrong")
	ctx, rec := kube.Fake(t.Context(), b, repo, secret)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	if err := newReconciler(cfg).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if pods := kube.Owned[agent.Pod](rec); res.State != gitk8s.Running || len(pods) != 1 || pods[0].Name != pod {
		t.Fatalf("result = %+v and Pods %v, want Running with Pod %s", res, pods, pod)
	}
}

func TestStartsOverWhenTheRunCantGoOn(t *testing.T) {
	withAgent(t)
	withUnion(t)
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, conflictingSum, map[string]string{"go.sum": "a v1\nc v1\n"})
	rec, err := reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || len(kube.Owned[agent.Pod](rec)) != 1 {
		t.Fatalf("result = %+v, want Running with an agent Pod", res)
	}

	// With go.sum union-merged, the agent's merge has no conflicts left.
	withUnion(t, "go.sum")
	rec, err = reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.Outputs["runs"] != "1" || len(kube.Owned[agent.Pod](rec)) != 0 {
		t.Fatalf("result = %+v, want Fixed by git without a Pod, counting the run", res)
	}
	if got := w.Fetch("c/x"); got != res.Outputs["fix"] {
		t.Errorf("c/x = %s, want the merge %s", got, res.Outputs["fix"])
	}
}

func TestStartsOverWhenTheBranchDivergesDuringARun(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, base := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	jobs := withJobs(t, func(_ *agent.Job, st *agent.JobState) agent.JobStatus {
		st.Runs, st.Pod, st.Attempt = st.Runs+1, fmt.Sprintf("conflicts-app-c-x-%d", st.Runs+1), 1
		return agent.JobStatus{Message: "the agent is working"}
	})
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running {
		t.Fatalf("result = %+v, want Running", res)
	}

	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	if len(*jobs) != 2 {
		t.Fatalf("ran %d jobs, want 2", len(*jobs))
	}
	want := &agent.Ref{Name: downstream + "c/x", Commit: e, DisplayName: "the external repository's c/x"}
	if got := (*jobs)[1].Checkout.Merge; !reflect.DeepEqual(got, want) {
		t.Errorf("the second job merges %+v, want %+v", got, want)
	}
}

func TestStartsOverWhenTheExternalHeadMovesDuringARun(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, base := setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
	jobs := withJobs(t, func(_ *agent.Job, st *agent.JobState) agent.JobStatus {
		st.Runs, st.Pod, st.Attempt = st.Runs+1, fmt.Sprintf("conflicts-app-c-x-%d", st.Runs+1), 1
		return agent.JobStatus{Message: "the agent is working"}
	})
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || res.Outputs["merge"] != e {
		t.Fatalf("result = %+v, want Running for %s", res, gitk8s.Short(e))
	}

	t.Log("The external repository force-pushes c/x to a head that drops the one that the run merges.")
	e2, _ := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal 2\nthree\n"})
	o.Status.Diverged.Commit = e2
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	if len(*jobs) != 2 {
		t.Fatalf("ran %d jobs, want 2", len(*jobs))
	}
	want := &agent.Ref{Name: downstream + "c/x", Commit: e2, DisplayName: "the external repository's c/x"}
	if got := (*jobs)[1].Checkout.Merge; !reflect.DeepEqual(got, want) {
		t.Errorf("the second job merges %+v, want %+v", got, want)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || res.Outputs["merge"] != e2 || res.Outputs["diverged"] != e2 || res.Outputs["runs"] != "2" {
		t.Errorf("result = %+v, want Running for %s, counting both runs", res, gitk8s.Short(e2))
	}
}

func TestStartsOverWhenMainRewindsBeforeThePodFetchesIt(t *testing.T) {
	for _, tc := range []struct {
		name string
		// waits is how many reconciles see the Pod's exit before the spec
		// holds main's new head.
		waits int
		// deploy changes the agent Pods' spec after those reconciles.
		deploy bool
	}{
		{name: "after the spec holds main's new head", waits: 2},
		{name: "when the spec already holds it"},
		{name: "after a deploy", waits: 1, deploy: true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			withAgent(t)
			srv := gittest.NewServer(t, "")
			b, w, base := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
			started := b.Spec.ParentHead
			rec, err := reconcile(t, srv, b, rules)
			if err != nil {
				t.Fatal(err)
			}
			p := kube.Owned[agent.Pod](rec)[0]
			p.Namespace, p.UID = "default", "uid-1"
			msg := "refs/heads/main no longer contains " + started
			rewound := func(p *agent.Pod) {
				p.Status = agent.PodStatus{Phase: "Failed", InitContainerStatuses: []agent.ContainerStatus{
					{Name: "prepare", State: agent.ContainerState{Terminated: &agent.Terminated{ExitCode: 3, Message: msg, FinishedAt: time.Now()}}},
				}}
			}
			rewound(p)
			w.Branch("main", base)
			moved := commit(w, "main rewinds", map[string]string{"a.txt": "one\nrewound\nthree\n"})
			w.Push("main")

			// The run gives back its place once, however many reconciles
			// see the Pod's exit.
			for range tc.waits {
				rec, err = reconcile(t, srv, b, rules, p)
				if err != nil {
					t.Fatal(err)
				}
				res := b.Status.Checks.Result
				if pods := kube.Owned[agent.Pod](rec); res.State != gitk8s.Running || res.Message != "waiting up to a minute for a run on the new commits: "+msg || len(pods) != 1 || pods[0].Name != p.Name {
					t.Fatalf("result = %+v and Pods %v, want Running with Pod %s", res, pods, p.Name)
				}
				if st := readState(res.Outputs); res.Outputs["merge"] != started || st.UID != "uid-1" || st.Refunded != "uid-1" || st.Runs != 0 {
					t.Errorf("outputs = %v, want the run that merges main at %s, given back", res.Outputs, started)
				}
			}
			if tc.deploy {
				t.Log("A deploy prepares the source again at once, and that Pod finds main rewound too.")
				runner.Model = "composer-3"
				rec, err = reconcile(t, srv, b, rules, p)
				if err != nil {
					t.Fatal(err)
				}
				res, pods := b.Status.Checks.Result, kube.Owned[agent.Pod](rec)
				if len(pods) != 1 || pods[0].Name == p.Name {
					t.Fatalf("result = %+v and Pods %v, want a new Pod", res, pods)
				}
				want := "preparing the source again in Pod " + pods[0].Name + ", because the run is still for the same commits after Pod " + p.Name + " found that c/x no longer points to " + b.Spec.Head + ", or " + msg
				if res.State != gitk8s.Running || res.Message != want || res.Outputs["merge"] != started || res.Outputs["runs"] != "1" {
					t.Fatalf("result = %+v, want Running with the run that merges main at %s in a new Pod", res, started)
				}
				p = pods[0]
				p.Namespace, p.UID = "default", "uid-2"
				rewound(p)
			}

			b.Spec.ParentHead = moved
			rec, err = reconcile(t, srv, b, rules, p)
			if err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			if res.State != gitk8s.Running || res.Outputs["merge"] != moved || res.Outputs["runs"] != "1" || res.Outputs["pod"] == p.Name || readState(res.Outputs).Refunded != "" {
				t.Fatalf("result = %+v, want Running with a new run that merges main at %s and counts once", res, moved)
			}
			if !slices.ContainsFunc(kube.Owned[agent.Pod](rec), func(q *agent.Pod) bool { return q.Name == res.Outputs["pod"] }) {
				t.Errorf("the check didn't declare the new run's Pod %s", res.Outputs["pod"])
			}
		})
	}
}

func TestKeepsTheRunsStateInItsOutputs(t *testing.T) {
	st := agent.JobState{Runs: 2, Pod: "conflicts-app-c-x-2", Attempt: 2, UID: "uid-2", Refunded: "uid-1", Done: true}
	got := readState(runOutputs(target{commit: strings.Repeat("a", 40)}, strings.Repeat("b", 40), &st))
	if *got != st {
		t.Errorf("state after the outputs = %+v, want %+v", *got, st)
	}
}

func TestFetchesTheResultAgainWhenGitFails(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	// Like RunJob, the fake reports a run whose JobState is done as done
	// without its result.
	withJobs(t, func(job *agent.Job, st *agent.JobState) agent.JobStatus {
		switch {
		case st.Done:
			return agent.JobStatus{Done: true, Message: "the run in Pod " + st.Pod + " already finished"}
		case st.Pod == "":
			st.Runs, st.Pod, st.Attempt = st.Runs+1, "conflicts-app-c-x-1", 1
			return agent.JobStatus{Message: "started Pod " + st.Pod}
		}
		st.Done = true
		res := resolution(resolvedA)
		res.MergeTree = mergeTree(t, w, job)
		return agent.JobStatus{Done: true, Message: "Both sides change the second line.", Result: res}
	})
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || res.Outputs["pod"] == "" {
		t.Fatalf("result = %+v, want Running with the agent's Pod", res)
	}

	t.Log("The run finishes while git fails.")
	repo, secret := srv.Repository("app", rules...)
	secret.Data["password"] = []byte("wrong")
	ctx, rec := kube.Fake(t.Context(), b, repo, secret)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	if err := newReconciler(cfg).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || !strings.HasPrefix(res.Message, "fetching the branch and main to commit the agent's resolution: ") || readState(res.Outputs).Done || rec.RequeueAfter() != 30*time.Second {
		t.Fatalf("result = %+v and RequeueAfter = %v, want Running with the run not done, again in 30 seconds", res, rec.RequeueAfter())
	}

	t.Log("Then the check fetches the result again and commits it, and the next reconcile deletes the Pod.")
	rec, err := reconcile(t, srv, b, rules)
	if err != nil {
		t.Fatal(err)
	}
	res = b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.Outputs["runs"] != "1" || !readState(res.Outputs).Done || rec.RequeueAfter() != time.Second {
		t.Fatalf("result = %+v and RequeueAfter = %v, want Fixed by the agent's one run, done, and a reconcile in a second", res, rec.RequeueAfter())
	}
	if got := w.Fetch("c/x"); got != res.Outputs["fix"] {
		t.Errorf("c/x = %s, want the merge %s", got, res.Outputs["fix"])
	}
}

func TestCommitsTheResultAgainWhenGitFailsToCommitIt(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	withJobs(t, func(job *agent.Job, st *agent.JobState) agent.JobStatus {
		switch {
		case st.Done:
			return agent.JobStatus{Done: true, Message: "the run in Pod " + st.Pod + " already finished"}
		case st.Pod == "":
			st.Runs, st.Pod, st.Attempt = st.Runs+1, "conflicts-app-c-x-1", 1
			return agent.JobStatus{Message: "started Pod " + st.Pod}
		}
		st.Done = true
		res := resolution(resolvedA)
		res.MergeTree = mergeTree(t, w, job)
		return agent.JobStatus{Done: true, Message: "Both sides change the second line.", Result: res}
	})
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}

	t.Log("The run finishes while git can't write objects.")
	bin := t.TempDir() + "/git"
	script := "#!/bin/sh\nfor a; do [ \"$a\" = commit-tree ] && { echo 'fatal: unable to write new object' >&2; exit 128; }; done\nexec git \"$@\"\n"
	if err := os.WriteFile(bin, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	repo, secret := srv.Repository("app", rules...)
	ctx, rec := kube.Fake(t.Context(), b, repo, secret)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	cfg.Git.Bin = bin
	if err := newReconciler(cfg).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || !strings.HasPrefix(res.Message, "committing the agent's resolution: ") || readState(res.Outputs).Done || rec.RequeueAfter() != 30*time.Second {
		t.Fatalf("result = %+v and RequeueAfter = %v, want Running with the run not done, again in 30 seconds", res, rec.RequeueAfter())
	}

	t.Log("Then the check commits the result.")
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	res = b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.Outputs["runs"] != "1" {
		t.Fatalf("result = %+v, want Fixed by the agent's one run", res)
	}
	if got := w.Fetch("c/x"); got != res.Outputs["fix"] {
		t.Errorf("c/x = %s, want the merge %s", got, res.Outputs["fix"])
	}
}

// resolution is the result of an agent that resolved a.txt's conflict.
func resolution(files ...agent.File) *agent.Result {
	cents := 1.5
	return &agent.Result{
		Verdict: agent.Pass, Summary: "kept both lines", Reasoning: "Both sides change the second line.",
		Model: "fake:composer-2.5", Usage: agent.Usage{InputTokens: 10, OutputTokens: 2}, CostCents: &cents, Files: files,
	}
}

var resolvedA = agent.File{Path: "a.txt", Mode: "100644", Content: []byte("one\nbranch\nmain\nthree\n")}

func TestCommitsTheAgentsResolution(t *testing.T) {
	for _, tc := range []struct {
		name     string
		external bool
	}{{name: "of main"}, {name: "of the external head", external: true}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "pw")
			mainFiles := map[string]string{"a.txt": "one\nmain\nthree\n", "go.sum": "a v1\nb v1\n"}
			b, w, base := setup(t, srv, mainFiles, map[string]string{"a.txt": "one\nbranch\nthree\n", "go.sum": "a v1\nc v1\n"})
			jobs := withJobs(t, finish(t, w, resolution(resolvedA)))
			head, merged := b.Spec.Head, b.Spec.ParentHead
			ref, task, title := &agent.Ref{Name: "refs/heads/main", Commit: merged, DisplayName: "main"}, instructions, "Merge main into c/x"
			var world []any
			if tc.external {
				var o *observed
				merged, o = diverge(w, b.Name, "c/x", base, mainFiles)
				ref = &agent.Ref{Name: downstream + "c/x", Commit: merged, DisplayName: "the external repository's c/x"}
				task, title = divergedInstructions+instructions, "Merge the external repository's c/x into c/x"
				world = append(world, o)
			}
			if _, err := reconcile(t, srv, b, rules, world...); err != nil {
				t.Fatal(err)
			}

			res := b.Status.Checks.Result
			fix := res.Outputs["fix"]
			if res.State != gitk8s.Fixed || fix == "" || res.Message != "the agent resolved the conflicts in a.txt; pushed "+gitk8s.Short(fix) {
				t.Fatalf("result = %+v, want Fixed with the agent's merge", res)
			}
			for k, want := range map[string]string{
				"merge": merged, "conflicts": "a.txt,go.sum", "runs": "1", "pod": "conflicts-app-c-x-1",
				"summary": "kept both lines", "model": "fake:composer-2.5", "inputTokens": "10", "outputTokens": "2", "costCents": "1.5",
			} {
				if got := res.Outputs[k]; got != want {
					t.Errorf("outputs[%s] = %q, want %q", k, got, want)
				}
			}
			if got := w.Fetch("c/x"); got != fix {
				t.Fatalf("c/x = %s, want the merge %s", got, fix)
			}
			want := head + " " + merged + "\n" + title + "\n\nkept both lines\n\na.txt\n\n" + git.FixerTrailer + ": conflicts"
			if got := w.Git("log", "-1", "--format=%P%n%B", "--end-of-options", fix); got != want {
				t.Errorf("merge's parents and message =\n%s\nwant\n%s", got, want)
			}
			if got := w.Show(fix, "a.txt"); got != "one\nbranch\nmain\nthree" {
				t.Errorf("a.txt = %q, want the agent's resolution", got)
			}
			if got := w.Show(fix, "go.sum"); got != "a v1\nc v1\nb v1" {
				t.Errorf("go.sum = %q, want git's union merge", got)
			}

			if len(*jobs) != 1 {
				t.Fatalf("ran %d jobs, want 1", len(*jobs))
			}
			job := (*jobs)[0]
			repo, _ := srv.Repository("app", rules...)
			wantCheckout := agent.Checkout{Branch: "c/x", Head: head, Parent: "main", Base: base, Merge: ref, Union: []string{"go.sum"}}
			if !reflect.DeepEqual(job.Checkout, wantCheckout) {
				t.Errorf("job's checkout = %+v, want %+v", job.Checkout, wantCheckout)
			}
			if job.Name != b.Name || job.Namespace != "default" || job.URL != repo.Spec.URL || !reflect.DeepEqual(job.Credentials, repo.Spec.SecretRef) ||
				job.Task != (agent.Task{Instructions: task, Edit: true}) || !slices.Equal(job.Tools, tools) || job.MaxRuns != 10 {
				t.Errorf("job = %+v", job)
			}
		})
	}
}

func TestRejectsABadResolution(t *testing.T) {
	for _, tc := range []struct {
		name  string
		files []agent.File
		want  string
	}{
		{name: "without changes", want: "conflict markers remain in a.txt"},
		{
			name:  "with a marker line",
			files: []agent.File{{Path: "a.txt", Mode: "100644", Content: []byte("one\nbranch\n=======\nmain\nthree\n")}},
			want:  "a.txt has more lines that start with ======= than its two sides, so conflict markers remain",
		},
		{
			name:  "with marker lines that have other labels",
			files: []agent.File{{Path: "a.txt", Mode: "100644", Content: []byte("one\n<<<<<<< ours\nbranch\nmain\n>>>>>>> theirs\nthree\n")}},
			want:  "a.txt has more lines that start with <<<<<<< than its two sides, so conflict markers remain",
		},
		{
			name:  "that changes another file",
			files: []agent.File{resolvedA, {Path: "b.txt", Mode: "100644", Content: []byte("b\n")}},
			want:  "the agent changed b.txt, which doesn't conflict",
		},
		{name: "that deletes the file", files: []agent.File{{Path: "a.txt", Deleted: true}}, want: "the agent deleted a.txt"},
		{
			name:  "that changes the file's mode",
			files: []agent.File{{Path: "a.txt", Mode: "100755", Content: resolvedA.Content}},
			want:  "the agent gave a.txt the mode 100755, which it has on neither side",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
			withJobs(t, finish(t, w, resolution(tc.files...)))
			head := b.Spec.Head
			if _, err := reconcile(t, srv, b, rules); err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			if want := "can't commit the agent's resolution: " + tc.want; res.State != gitk8s.Failed || res.Message != want {
				t.Errorf("result = %+v, want Failed with %q", res, want)
			}
			if res.Outputs["runs"] != "1" || res.Outputs["inputTokens"] != "10" {
				t.Errorf("outputs = %v, want the run and what it used", res.Outputs)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestRejectsAResolutionOfAnotherMerge(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	head := b.Spec.Head
	other, merged := w.Git("rev-parse", "--verify", "--end-of-options", head+"^{tree}"), ""
	withJobs(t, func(job *agent.Job, st *agent.JobState) agent.JobStatus {
		s := finish(t, w, resolution(resolvedA))(job, st)
		if s.Result != nil {
			merged, s.Result.MergeTree = s.Result.MergeTree, other
		}
		return s
	})
	if _, err := reconcile(t, srv, b, rules); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	want := "can't commit the agent's resolution: the agent resolved a merge with the tree " + other + ", but the check's merge has the tree " + merged
	if res.State != gitk8s.Failed || res.Message != want {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestReportsARunThatDoesntResolve(t *testing.T) {
	for _, tc := range []struct {
		name, want string
		status     agent.JobStatus
	}{{
		name: "when the agent fails",
		want: "the agent couldn't resolve the conflicts: The two sides contradict each other.",
		status: agent.JobStatus{Done: true, Message: "The two sides contradict each other.", Result: &agent.Result{
			Verdict: agent.Fail, Summary: "can't resolve a.txt", Reasoning: "The two sides contradict each other.",
			Model: "fake:composer-2.5", Usage: agent.Usage{InputTokens: 10},
		}},
	}, {
		name: "when the run fails",
		want: "the agent failed in Pod conflicts-app-c-x-1: out of time",
		status: agent.JobStatus{Done: true, Message: "the agent failed in Pod conflicts-app-c-x-1: out of time", Failed: &agent.Result{
			Verdict: agent.Fail, Model: "fake:composer-2.5", Usage: agent.Usage{InputTokens: 10}, Error: "out of time",
		}},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			withJobs(t, func(_ *agent.Job, st *agent.JobState) agent.JobStatus {
				st.Runs, st.Pod = st.Runs+1, "conflicts-app-c-x-1"
				return tc.status
			})
			srv := gittest.NewServer(t, "")
			b, _, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
			head := b.Spec.Head
			if _, err := reconcile(t, srv, b, rules); err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			if res.State != gitk8s.Failed || res.Message != tc.want {
				t.Errorf("result = %+v, want Failed with %q", res, tc.want)
			}
			if res.Outputs["runs"] != "1" || res.Outputs["merge"] != b.Spec.ParentHead || res.Outputs["inputTokens"] != "10" || res.Outputs["model"] != "fake:composer-2.5" {
				t.Errorf("outputs = %v, want the run and what it used", res.Outputs)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestMergesTheExternalHead(t *testing.T) {
	for _, tc := range []struct {
		name, want, file, content string
		external                  map[string]string
	}{{
		name:     "without conflicts",
		want:     "the branch diverged from the external repository's c/x at ",
		external: map[string]string{"d.txt": "external\n"},
		file:     "d.txt", content: "external",
	}, {
		name:     "with union paths",
		want:     "merging the external repository's c/x conflicts in go.sum, which git merged with its union driver",
		external: map[string]string{"go.sum": "a v1\nd v1\n"},
		file:     "go.sum", content: "a v1\nc v1\nd v1",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "pw")
			// main conflicts with c/x, but the divergence comes first.
			b, w, _ := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n", "go.sum": "a v1\nc v1\n"})
			head := b.Spec.Head
			e, o := diverge(w, b.Name, "c/x", head+"~1", tc.external)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			fix := res.Outputs["fix"]
			if res.State != gitk8s.Fixed || fix == "" || !strings.HasPrefix(res.Message, tc.want) {
				t.Fatalf("result = %+v, want Fixed with %q", res, tc.want)
			}
			if res.Outputs["diverged"] != e || res.Outputs["merge"] != e {
				t.Errorf("outputs = %v, want the external head %s", res.Outputs, e)
			}
			if got := w.Fetch("c/x"); got != fix {
				t.Fatalf("c/x = %s, want the merge %s", got, fix)
			}
			msg := w.Git("log", "-1", "--format=%P%n%B", "--end-of-options", fix)
			if !strings.HasPrefix(msg, head+" "+e+"\nMerge the external repository's c/x into c/x\n\n") || !strings.HasSuffix(msg, "\n"+git.FixerTrailer+": conflicts") {
				t.Errorf("merge's parents and message =\n%s", msg)
			}
			if got := w.Show(fix, tc.file); got != tc.content {
				t.Errorf("%s = %q, want %q", tc.file, got, tc.content)
			}

			b.Spec.Head = fix
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasPrefix(res.Message, "contains the external repository's c/x at ") || res.Outputs["diverged"] != e {
				t.Errorf("result after the merge = %+v, want Passed", res)
			}
		})
	}
}

func TestPassesWhenTheExternalHeadContainsTheBranch(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"c.txt": "branch\n"})
	head := b.Spec.Head
	_, o := diverge(w, b.Name, "c/x", head, map[string]string{"d.txt": "external\n"})
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasSuffix(res.Message, "already contains the branch's head") {
		t.Errorf("result = %+v, want Passed", res)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestStartsAnAgentForTheExternalHead(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "")
	b, w, base := setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
	rec, err := reconcile(t, srv, b, rules, o)
	if err != nil {
		t.Fatal(err)
	}
	pods := kube.Owned[agent.Pod](rec)
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || len(pods) != 1 || res.Outputs["diverged"] != e || res.Outputs["conflicts"] != "a.txt" {
		t.Fatalf("result = %+v and %d Pods, want Running with one Pod", res, len(pods))
	}
	if task := agentTask(t, pods[0]); task.Instructions != divergedInstructions+instructions || task.MergeName != "the external repository's c/x" || task.MergeHead != e {
		t.Errorf("the agent's task = %+v, want a merge of the external head", task)
	}
	if got := prepareEnv(pods[0], "MERGE_REF"); got != downstream+"c/x" {
		t.Errorf("MERGE_REF = %q", got)
	}
}

func TestRejectsAnInvalidDivergence(t *testing.T) {
	for _, tc := range []struct {
		name, want string
		d          func(head string) gitk8s.Divergence
	}{{
		name: "commit",
		want: `status.diverged.commit is "--upload-pack=touch /tmp/x", which isn't a commit ID`,
		d: func(string) gitk8s.Divergence {
			return gitk8s.Divergence{Commit: "--upload-pack=touch /tmp/x", Ref: downstream + "c/x"}
		},
	}, {
		name: "ref",
		want: `status.diverged.ref is "--upload-pack=touch /tmp/x", but the mirror keeps the external repository's c/x at refs/git-k8s/downstream/heads/c/x`,
		d: func(head string) gitk8s.Divergence {
			return gitk8s.Divergence{Commit: head, Ref: "--upload-pack=touch /tmp/x"}
		},
	}, {
		name: "another ref",
		want: `status.diverged.ref is "refs/pull/1/head", but the mirror keeps the external repository's c/x at refs/git-k8s/downstream/heads/c/x`,
		d: func(head string) gitk8s.Divergence {
			return gitk8s.Divergence{Commit: head, Ref: "refs/pull/1/head"}
		},
	}, {
		name: "another branch's ref",
		want: `status.diverged.ref is "refs/git-k8s/downstream/heads/main", but the mirror keeps the external repository's c/x at refs/git-k8s/downstream/heads/c/x`,
		d: func(head string) gitk8s.Divergence {
			return gitk8s.Divergence{Commit: head, Ref: downstream + "main"}
		},
	}, {
		name: "base",
		want: `status.diverged.base is "--upload-pack=touch /tmp/x", which isn't a commit ID`,
		d: func(head string) gitk8s.Divergence {
			return gitk8s.Divergence{Commit: head, Ref: downstream + "c/x", Base: "--upload-pack=touch /tmp/x"}
		},
	}, {
		name: "deletion without a base",
		want: `status.diverged.base is "", which isn't a commit ID`,
		d:    func(string) gitk8s.Divergence { return gitk8s.Divergence{} },
	}} {
		t.Run(tc.name, func(t *testing.T) {
			withAgent(t)
			srv := gittest.NewServer(t, "")
			b, w, base := setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"a.txt": "one\nbranch\nthree\n"})
			e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
			*o.Status.Diverged = tc.d(e)
			rec, err := reconcile(t, srv, b, rules, o)
			if err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != tc.want {
				t.Errorf("result = %+v, want Failed with %q", res, tc.want)
			}
			if pods := kube.Owned[agent.Pod](rec); len(pods) != 0 {
				t.Errorf("started %d agent Pods, want none", len(pods))
			}
		})
	}
}

func TestLeavesABranchThatTheExternalRepositoryDeleted(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "")
	b, _, base := setup(t, srv, conflictingA, map[string]string{"a.txt": "one\nbranch\nthree\n"})
	head := b.Spec.Head
	o := &observed{Object: kube.Meta(b.Name, nil)}
	o.Namespace = "default"
	o.Status.Diverged = &gitk8s.Divergence{Base: base}
	rec, err := reconcile(t, srv, b, rules, o)
	if err != nil {
		t.Fatal(err)
	}
	want := "the external repository deleted c/x, which changed in git-k8s since they last synced at " + gitk8s.Short(base) +
		"; push c/x to the external repository again to keep its changes, or delete it in git-k8s to drop them"
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["synced"] != base || res.Outputs["diverged"] != "" {
		t.Errorf("result = %+v, want Failed with %q and the synced head in the outputs", res, want)
	}
	if pods := kube.Owned[agent.Pod](rec); len(pods) != 0 {
		t.Errorf("started %d agent Pods, want none", len(pods))
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestRunsAgainForAnotherMerge(t *testing.T) {
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec.ParentHead = "p1"
	diverged := func(d gitk8s.Divergence) *observed {
		o := &observed{Object: kube.Meta(b.Name, nil)}
		o.Namespace = "default"
		o.Status.Diverged = &d
		return o
	}
	o := diverged(gitk8s.Divergence{Commit: "e1", Ref: downstream + "c/x"})
	synced := diverged(gitk8s.Divergence{Commit: "e1", Ref: downstream + "c/x", Base: "s1"})
	deleted := diverged(gitk8s.Divergence{Base: "s1"})
	for _, tc := range []struct {
		name    string
		outputs map[string]string
		world   []any
		want    bool
	}{
		{name: "without a merge", want: false},
		{name: "after merging main's head", outputs: map[string]string{"merge": "p1"}, want: false},
		{name: "after merging an earlier head of main", outputs: map[string]string{"merge": "p0"}, want: true},
		{name: "after merging the external head", outputs: map[string]string{"diverged": "e1", "merge": "e1"}, world: []any{o}, want: false},
		{name: "after the branch diverged", outputs: map[string]string{"merge": "p1"}, world: []any{o}, want: true},
		{name: "after the external head moved", outputs: map[string]string{"diverged": "e0", "merge": "e0"}, world: []any{o}, want: true},
		{name: "after the divergence cleared", outputs: map[string]string{"diverged": "e1", "merge": "e1"}, want: true},
		{name: "after resolving a divergence since the sides synced", outputs: map[string]string{"diverged": "e1", "synced": "s1", "merge": "e1"}, world: []any{synced}, want: false},
		{name: "after the sides synced again", outputs: map[string]string{"diverged": "e1", "synced": "s0", "merge": "e1"}, world: []any{synced}, want: true},
		{name: "after the external repository deleted the branch", outputs: map[string]string{"merge": "p1"}, world: []any{deleted}, want: true},
		{name: "after failing on the deletion", outputs: map[string]string{"synced": "s1"}, world: []any{deleted}, want: false},
		{name: "after the deletion cleared", outputs: map[string]string{"synced": "s1"}, want: true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, _ := kube.Fake(t.Context(), b, tc.world...)
			prev := &gitk8s.CheckResult{State: gitk8s.Failed, Outputs: tc.outputs}
			if got := stale(ctx, &b.ObjectMeta, &b.Spec, prev); got != tc.want {
				t.Errorf("stale = %t, want %t", got, tc.want)
			}
		})
	}
}

// rewound pushes c/x as a branch that last synced with the external
// repository at synced, a commit on top of base that adds s.txt, and that
// changed since then with the commits that branch makes on top of synced.
// It returns c/x's view, base, and synced.
func rewound(t *testing.T, srv *gittest.Server, branch func(w *gittest.Work, b *Branch)) (b *Branch, w *gittest.Work, base, synced string) {
	b, w, base = setup(t, srv, map[string]string{"b.txt": "main\n"}, map[string]string{"s.txt": "synced\n"})
	synced = b.Spec.Head
	branch(w, b)
	b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Push("c/x")
	return b, w, base, synced
}

// authorAndMessage is commit's author, author date, and message.
func authorAndMessage(w *gittest.Work, commit string) string {
	return w.Git("log", "-1", "--format=%an <%ae> %ad%n%B", "--end-of-options", commit)
}

func TestReplaysTheBranchOntoARewoundExternalHead(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
		commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
		commit(w, "branch edit 2", map[string]string{"a.txt": "one\ntwo\nbranch\n"})
	})
	head := b.Spec.Head
	// The external repository drops synced's commit, and changes a.txt.
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "external\ntwo\nthree\n"})
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "the external repository's c/x rewound since it last synced at " + gitk8s.Short(synced) + "; replayed the branch's commits since then onto it; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "external" || res.Outputs["synced"] != synced {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replays %s", got, fix)
	}
	for i, orig := range []string{head, head + "~1"} {
		replay := fmt.Sprintf("%s~%d", fix, i)
		if got, want := authorAndMessage(w, replay), authorAndMessage(w, orig); got != want {
			t.Errorf("replay %s's author and message = %q, want %q", replay, got, want)
		}
		if got := w.Git("log", "-1", "--format=%cn <%ce>", "--end-of-options", replay); got != "git-k8s <git-k8s@example.com>" {
			t.Errorf("replay %s's committer = %q", replay, got)
		}
	}
	if got := w.Git("rev-parse", "--verify", "--end-of-options", fix+"~2"); got != e {
		t.Errorf("the replays start at %s, want the external head %s", got, e)
	}
	if got := w.Show(fix, "a.txt"); got != "external\ntwo\nbranch" {
		t.Errorf("a.txt = %q, want both sides' changes", got)
	}
	if got := files(w, fix); got != "a.txt\nc.txt\ngo.sum" {
		t.Errorf("files = %q, want c.txt, and not s.txt, which the external repository removed", got)
	}

	b.Spec.Head = fix
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want = "the branch keeps every change that the external repository's c/x at " + gitk8s.Short(e) + " made since they last synced at " + gitk8s.Short(synced)
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || res.Message != want {
		t.Errorf("result after the replays = %+v, want Passed with %q", res, want)
	}
}

func TestSkipsChangesThatTheRewoundExternalHeadHas(t *testing.T) {
	for _, tc := range []struct {
		name, want string
		// replays counts the replays on top of the external head.
		replays int
	}{
		{name: "for some commits", want: "; replayed the branch's commits since then onto it, skipping those whose changes it already has", replays: 1},
		{name: "for every commit", want: ", and already has every change that the branch made since then"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
				commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
				if tc.replays > 0 {
					commit(w, "branch edit 2", map[string]string{"e.txt": "branch\n"})
				}
			})
			// The external repository has the branch's first change in a
			// commit that changes more, so it isn't a replay.
			e, o := diverge(w, b.Name, "c/x", base, map[string]string{"c.txt": "branch\n", "d.txt": "external\n"})
			syncedAt(w, o, "c/x", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			fix := res.Outputs["fix"]
			want := "the external repository's c/x rewound since it last synced at " + gitk8s.Short(synced) + tc.want + "; pushed " + gitk8s.Short(fix)
			if res.State != gitk8s.Fixed || res.Message != want {
				t.Fatalf("result = %+v, want Fixed with %q", res, want)
			}
			if got := w.Fetch("c/x"); got != fix {
				t.Fatalf("c/x = %s, want %s", got, fix)
			}
			if got := w.Git("rev-list", "--count", "--end-of-options", e+".."+fix); got != strconv.Itoa(tc.replays) {
				t.Errorf("c/x has %s commits on top of the external head, want %d", got, tc.replays)
			}
		})
	}
}

func TestReplaysTheBranchAsOneCommit(t *testing.T) {
	for _, tc := range []struct {
		name string
		// branch makes c/x's commits since synced, and returns the one that
		// can't be replayed by itself.
		branch   func(w *gittest.Work, b *Branch) string
		external map[string]string
		// why says why the commit, which it formats, can't be replayed, and
		// want is the rest of the message, which formats the head where
		// the sides synced and the external head, if it has verbs.
		why, want string
		body      string
		files     map[string]string
	}{{
		name: "when a replay conflicts",
		branch: func(w *gittest.Work, _ *Branch) string {
			c := commit(w, "branch edit", map[string]string{"a.txt": "one\nbranch\nthree\n"})
			commit(w, "branch revert", map[string]string{"a.txt": "one\ntwo\nthree\n", "c.txt": "branch\n"})
			return c
		},
		external: map[string]string{"a.txt": "one\nexternal\nthree\n"},
		why:      "replaying commit %s of the branch conflicts in a.txt",
		want:     "replayed the branch's commits since %s onto the external repository's c/x at %s as one commit",
		files:    map[string]string{"a.txt": "one\nexternal\nthree", "c.txt": "branch"},
	}, {
		name: "when the branch merged main",
		branch: func(w *gittest.Work, b *Branch) string {
			commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
			w.Git("merge", "--quiet", "--no-edit", "--end-of-options", b.Spec.ParentHead)
			return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
		},
		external: map[string]string{"a.txt": "one\nexternal\nthree\n"},
		why:      "commit %s of the branch is a merge, which has no replay",
		want:     "replayed the branch's commits since %s onto the external repository's c/x at %s as one commit",
		files:    map[string]string{"a.txt": "one\nexternal\nthree", "b.txt": "main", "c.txt": "branch"},
	}, {
		name: "with union paths",
		branch: func(w *gittest.Work, _ *Branch) string {
			return commit(w, "branch edit", map[string]string{"go.sum": "a v1\nc v1\n"})
		},
		external: map[string]string{"go.sum": "a v1\nd v1\n"},
		why:      "replaying commit %s of the branch conflicts in go.sum",
		want:     "replaying the branch onto the external repository's c/x conflicts in go.sum, which git merged with its union driver",
		body:     "Git merged these files with its union driver, which keeps the lines of both sides:\n\ngo.sum\n\n",
		files:    map[string]string{"go.sum": "a v1\nc v1\nd v1"},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "pw")
			var stuck string
			b, w, base, synced := rewound(t, srv, func(w *gittest.Work, b *Branch) { stuck = tc.branch(w, b) })
			head := b.Spec.Head
			e, o := diverge(w, b.Name, "c/x", base, tc.external)
			syncedAt(w, o, "c/x", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			res := b.Status.Checks.Result
			fix := res.Outputs["fix"]
			want := tc.want
			if strings.Contains(want, "%s") {
				want = fmt.Sprintf(want, gitk8s.Short(synced), gitk8s.Short(e))
			}
			want = fmt.Sprintf(tc.why, gitk8s.Short(stuck)) + "; " + want + "; pushed " + gitk8s.Short(fix)
			if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "external" || res.Outputs["merge"] != e {
				t.Fatalf("result = %+v, want Fixed with %q", res, want)
			}
			if got := w.Fetch("c/x"); got != fix {
				t.Fatalf("c/x = %s, want the replay %s", got, fix)
			}
			wantMsg := e + "\nReplay c/x onto the external repository's c/x\n\n" +
				"The external repository rewound c/x since it last synced with git-k8s,\n" +
				"so this commit replays the changes that c/x made since then onto the\n" +
				"external repository's head, as one commit:\n\n" + synced + ".." + head + "\n\n" + tc.body + git.FixerTrailer + ": conflicts"
			if got := w.Git("log", "-1", "--format=%P%n%B", "--end-of-options", fix); got != wantMsg {
				t.Errorf("replay's parents and message =\n%s\nwant\n%s", got, wantMsg)
			}
			for file, content := range tc.files {
				if got := w.Show(fix, file); got != content {
					t.Errorf("%s = %q, want %q", file, got, content)
				}
			}
			if got := files(w, fix); strings.Contains(got, "s.txt") {
				t.Errorf("files = %q, want s.txt, which the external repository removed, left out", got)
			}

			b.Spec.Head = fix
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasPrefix(res.Message, "the branch keeps every change that the external repository's c/x at ") {
				t.Errorf("result after the replay = %+v, want Passed", res)
			}
		})
	}
}

func TestStartsAnAgentToReplayTheBranch(t *testing.T) {
	withAgent(t)
	srv := gittest.NewServer(t, "")
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
		commit(w, "branch edit", map[string]string{"a.txt": "one\nbranch\nthree\n"})
	})
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
	syncedAt(w, o, "c/x", synced)
	rec, err := reconcile(t, srv, b, rules, o)
	if err != nil {
		t.Fatal(err)
	}
	res, pods := b.Status.Checks.Result, kube.Owned[agent.Pod](rec)
	if res.State != gitk8s.Running || len(pods) != 1 {
		t.Fatalf("result = %+v and %d Pods, want Running with one Pod", res, len(pods))
	}
	if want := "replaying commit " + gitk8s.Short(b.Spec.Head) + " of the branch conflicts in a.txt; started Pod " + pods[0].Name; res.Message != want {
		t.Errorf("message = %q, want %q", res.Message, want)
	}
	for k, want := range map[string]string{"rewound": "external", "merge": e, "base": synced, "synced": synced, "diverged": e, "conflicts": "a.txt"} {
		if got := res.Outputs[k]; got != want {
			t.Errorf("outputs[%s] = %q, want %q", k, got, want)
		}
	}
	task := agentTask(t, pods[0])
	if task.Instructions != replayInstructions+instructions || task.Base != synced || task.MergeName != "the external repository's c/x" || task.MergeHead != e {
		t.Errorf("the agent's task = %+v, want a replay onto the external head", task)
	}
	for name, want := range map[string]string{"MERGE_REF": downstream + "c/x", "MERGE_HEAD": e, "BASE": synced} {
		if got := prepareEnv(pods[0], name); got != want {
			t.Errorf("%s = %q, want %q", name, got, want)
		}
	}

	rec, err = reconcile(t, srv, b, rules, o)
	if err != nil {
		t.Fatal(err)
	}
	res, again := b.Status.Checks.Result, kube.Owned[agent.Pod](rec)
	if res.State != gitk8s.Running || len(again) != 1 || again[0].Name != pods[0].Name || res.Outputs["rewound"] != "external" {
		t.Errorf("result = %+v and Pods %v, want Running with Pod %s", res, again, pods[0].Name)
	}

	t.Log("When the sides sync at another head, the run is for another replay.")
	syncedAt(w, o, "c/x", base)
	rec, err = reconcile(t, srv, b, rules, o)
	if err != nil {
		t.Fatal(err)
	}
	if res, pods := b.Status.Checks.Result, kube.Owned[agent.Pod](rec); len(pods) == 1 && pods[0].Name == again[0].Name {
		t.Errorf("result = %+v, want the run that replays onto %s gone", res, gitk8s.Short(synced))
	}
}

func TestCommitsTheAgentsReplay(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
		commit(w, "branch edit", map[string]string{"a.txt": "one\nbranch\nthree\n", "go.sum": "a v1\nc v1\n"})
	})
	head := b.Spec.Head
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n", "go.sum": "a v1\nb v1\n"})
	syncedAt(w, o, "c/x", synced)
	resolved := agent.File{Path: "a.txt", Mode: "100644", Content: []byte("one\nbranch\nexternal\nthree\n")}
	jobs := withJobs(t, finish(t, w, resolution(resolved)))
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "replaying commit " + gitk8s.Short(head) + " of the branch conflicts in a.txt, go.sum; the agent resolved the conflicts in a.txt; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "external" {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replay %s", got, fix)
	}
	wantMsg := e + "\nReplay c/x onto the external repository's c/x\n\n" +
		"The external repository rewound c/x since it last synced with git-k8s,\n" +
		"so this commit replays the changes that c/x made since then onto the\n" +
		"external repository's head, as one commit:\n\n" + synced + ".." + head + "\n\nkept both lines\n\na.txt\n\n" + git.FixerTrailer + ": conflicts"
	if got := w.Git("log", "-1", "--format=%P%n%B", "--end-of-options", fix); got != wantMsg {
		t.Errorf("replay's parents and message =\n%s\nwant\n%s", got, wantMsg)
	}
	if got := w.Show(fix, "a.txt"); got != "one\nbranch\nexternal\nthree" {
		t.Errorf("a.txt = %q, want the agent's resolution", got)
	}
	if got := w.Show(fix, "go.sum"); got != "a v1\nc v1\nb v1" {
		t.Errorf("go.sum = %q, want git's union merge", got)
	}
	if got := files(w, fix); strings.Contains(got, "s.txt") {
		t.Errorf("files = %q, want s.txt, which the external repository removed, left out", got)
	}
	if len(*jobs) != 1 {
		t.Fatalf("ran %d jobs, want 1", len(*jobs))
	}
	job := (*jobs)[0]
	wantCheckout := agent.Checkout{
		Branch: "c/x", Head: head, Parent: "main", Base: synced,
		Merge: &agent.Ref{Name: downstream + "c/x", Commit: e, DisplayName: "the external repository's c/x"}, Union: []string{"go.sum"},
	}
	if !reflect.DeepEqual(job.Checkout, wantCheckout) || job.Task.Instructions != replayInstructions+instructions {
		t.Errorf("job = %+v, want a replay of c/x onto the external head", job)
	}
}

func TestReplaysTheExternalCommitsOntoARewoundBranch(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	// c/x drops synced's commit, and adds its own.
	w.Branch("c/x", base)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	w.Push("c/x")
	head := b.Spec.Head
	e1, o := diverge(w, b.Name, "c/x", synced, map[string]string{"d.txt": "external\n"})
	e := commit(w, "external edit 2", map[string]string{"a.txt": "one\ntwo\nexternal\n"})
	w.PushRef(downstream + "c/x")
	o.Status.Diverged.Commit = e
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "the branch rewound since it last synced at " + gitk8s.Short(synced) + "; replayed the commits that the external repository's c/x added since then onto it; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "branch" {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replays %s", got, fix)
	}
	if got := w.Git("rev-parse", "--verify", "--end-of-options", fix+"~2"); got != head {
		t.Errorf("the replays start at %s, want the branch's head %s", got, head)
	}
	for i, orig := range []string{e, e1} {
		replay := fmt.Sprintf("%s~%d", fix, i)
		if got, want := authorAndMessage(w, replay), authorAndMessage(w, orig); got != want {
			t.Errorf("replay %s's author and message = %q, want %q", replay, got, want)
		}
		if got, want := w.Git("diff", "--end-of-options", replay+"~1", replay), w.Git("diff", "--end-of-options", orig+"~1", orig); got != want {
			t.Errorf("replay %s's change =\n%s\nwant\n%s", replay, got, want)
		}
	}
	if got := files(w, fix); got != "a.txt\nc.txt\nd.txt\ngo.sum" {
		t.Errorf("files = %q, want c.txt and d.txt, and not s.txt, which the branch removed", got)
	}

	b.Spec.Head = fix
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want = "the branch keeps every change that the external repository's c/x at " + gitk8s.Short(e) + " made since they last synced at " + gitk8s.Short(synced)
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || res.Message != want {
		t.Errorf("result after the replays = %+v, want Passed with %q", res, want)
	}
}

func TestLeavesARewoundBranchWhoseExternalCommitsDontReplay(t *testing.T) {
	for _, tc := range []struct {
		name string
		// branch makes c/x's commits on top of base, and external the
		// external repository's on top of synced. external returns the
		// commit that doesn't replay.
		branch   func(w *gittest.Work)
		external func(w *gittest.Work, b *Branch) string
		why      string
	}{{
		name:     "when a replay conflicts",
		branch:   func(w *gittest.Work) { commit(w, "branch edit", map[string]string{"a.txt": "one\nbranch\nthree\n"}) },
		external: func(w *gittest.Work, _ *Branch) string { return commit(w, "external edit", conflictingA) },
		why:      "replaying commit %s of the external repository's c/x conflicts in a.txt",
	}, {
		name:     "when a replay changes another file",
		branch:   func(w *gittest.Work) { w.Git("mv", "--end-of-options", "a.txt", "r.txt"); w.Commit("rename a.txt") },
		external: func(w *gittest.Work, _ *Branch) string { return commit(w, "external edit", conflictingA) },
		why:      "the replay of commit %s of the external repository's c/x doesn't change the same lines in the same files as the commit",
	}, {
		name:     "when a commit changes no file",
		branch:   func(w *gittest.Work) { commit(w, "branch edit", map[string]string{"c.txt": "branch\n"}) },
		external: func(w *gittest.Work, _ *Branch) string { return w.Commit("empty") },
		why:      "commit %s of the external repository's c/x changes no file, so it has no replay",
	}, {
		name:   "when a commit is a merge",
		branch: func(w *gittest.Work) { commit(w, "branch edit", map[string]string{"c.txt": "branch\n"}) },
		external: func(w *gittest.Work, b *Branch) string {
			w.Git("merge", "--quiet", "--no-edit", "--end-of-options", b.Spec.ParentHead)
			return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
		},
		why: "commit %s of the external repository's c/x is a merge, which has no replay",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
			w.Branch("c/x", base)
			tc.branch(w)
			b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
			w.Push("c/x")
			head := b.Spec.Head
			w.Branch("external", synced)
			stuck := tc.external(w, b)
			w.PushRef(downstream + "c/x")
			o := &observed{Object: kube.Meta(b.Name, nil)}
			o.Namespace = "default"
			o.Status.Diverged = &gitk8s.Divergence{Commit: w.Git("rev-parse", "--verify", "--end-of-options", "HEAD"), Ref: downstream + "c/x"}
			syncedAt(w, o, "c/x", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			want := "the branch rewound since it last synced at " + gitk8s.Short(synced) + ", and " + fmt.Sprintf(tc.why, gitk8s.Short(stuck)) + ", so the check leaves the divergence for a person"
			if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "branch" {
				t.Errorf("result = %+v, want Failed with %q", res, want)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestResolvesADivergenceInWhichBothSidesRewound(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	// The sides synced at s2, on top of s1. c/x drops s2 and adds a commit,
	// and the external repository drops both and adds its own.
	b, w, base, s1 := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	w.Branch("synced", s1)
	s2 := commit(w, "synced 2", map[string]string{"s2.txt": "synced\n"})
	w.Branch("c/x", s1)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	w.Push("c/x")
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"d.txt": "external\n"})
	syncedAt(w, o, "c/x", s2)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "the external repository's c/x rewound since it last synced at " + gitk8s.Short(s2) + "; replayed the branch's commits since then onto it; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "both" {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replay %s", got, fix)
	}
	if got := w.Git("log", "--format=%P %s", "--end-of-options", fix); !strings.HasPrefix(got, e+" branch edit\n") {
		t.Errorf("c/x's history =\n%s\nwant the branch's commit replayed onto the external head", got)
	}
	if got := files(w, fix); got != "a.txt\nc.txt\nd.txt\ngo.sum" {
		t.Errorf("files = %q, want neither s.txt, which the external repository removed, nor s2.txt, which both sides removed", got)
	}
}

func TestLeavesADivergenceInWhichBothSidesKeptWhatTheOtherRemoved(t *testing.T) {
	srv := gittest.NewServer(t, "")
	// The sides synced at a merge of s1 and s2. c/x keeps s1 and drops s2,
	// and the external repository keeps s2 and drops s1.
	b, w, base, s1 := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	w.Branch("s2", base)
	s2 := commit(w, "synced 2", map[string]string{"s2.txt": "synced\n"})
	w.Git("merge", "--quiet", "--no-edit", "--end-of-options", s1)
	synced := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Branch("c/x", s1)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	w.Push("c/x")
	head := b.Spec.Head
	_, o := diverge(w, b.Name, "c/x", s2, map[string]string{"d.txt": "external\n"})
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the branch and the external repository's c/x both rewound since they last synced at " + gitk8s.Short(synced) + ", and each kept commits that the other removed, so the check leaves the divergence for a person"
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "both" {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

// twins is f.txt with 60 numbered lines, except that lines 10 and 50 say
// foo, or bar if they're in at. A commit that changes line 10 from foo to
// bar has the same patch ID as one that changes line 50, because a patch
// ID ignores where in a file a change is.
func twins(at ...int) map[string]string {
	var b strings.Builder
	for i := 1; i <= 60; i++ {
		switch {
		case slices.Contains(at, i):
			b.WriteString("bar\n")
		case i == 10 || i == 50:
			b.WriteString("foo\n")
		default:
			fmt.Fprintf(&b, "line %d\n", i)
		}
	}
	return map[string]string{"f.txt": b.String()}
}

func TestReplaysAChangeThatTheRewoundExternalHeadMakesElsewhere(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, _ := setup(t, srv, map[string]string{"b.txt": "main\n"}, twins())
	p := b.Spec.Head
	synced := commit(w, "synced", map[string]string{"s.txt": "synced\n"})
	b.Spec.Head = commit(w, "branch edit", twins(10))
	w.Push("c/x")
	// The external repository drops synced's commit, and makes the
	// branch's change to line 50 instead of line 10.
	e, o := diverge(w, b.Name, "c/x", p, twins(50))
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "the external repository's c/x rewound since it last synced at " + gitk8s.Short(synced) + "; replayed the branch's commits since then onto it; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "external" {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replay %s", got, fix)
	}
	if got, want := w.Show(fix, "f.txt"), strings.TrimSuffix(twins(10, 50)["f.txt"], "\n"); got != want {
		t.Errorf("f.txt = %q, want both sides' changes", got)
	}

	b.Spec.Head = fix
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want = "the branch keeps every change that the external repository's c/x at " + gitk8s.Short(e) + " made since they last synced at " + gitk8s.Short(synced)
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || res.Message != want {
		t.Errorf("result after the replay = %+v, want Passed with %q", res, want)
	}
}

func TestLeavesAnExternalChangeThatTheRewoundBranchMakesElsewhere(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _ := setup(t, srv, map[string]string{"b.txt": "main\n"}, twins())
	p := b.Spec.Head
	synced := commit(w, "synced", map[string]string{"s.txt": "synced\n"})
	// c/x drops synced's commit, and makes the external repository's
	// change to line 10 instead of line 50.
	w.Branch("c/x", p)
	b.Spec.Head = commit(w, "branch edit", twins(10))
	w.Push("c/x")
	head := b.Spec.Head
	_, o := diverge(w, b.Name, "c/x", synced, twins(50))
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the branch rewound since it last synced at " + gitk8s.Short(synced) + ", and the branch with replays of the commits of the external repository's c/x doesn't have every change that the external repository's c/x made, so the check leaves the divergence for a person"
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "branch" {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestLeavesAFileThatTheRewoundBranchBringsBack(t *testing.T) {
	srv := gittest.NewServer(t, "")
	// c/x drops synced's commit, replays the external repository's
	// commit, which deletes a.txt, and then adds a.txt back.
	b, w, _, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
		w.Branch("c/x", "HEAD~1")
		w.Git("rm", "--quiet", "--end-of-options", "a.txt")
		w.Commit("delete a.txt")
		commit(w, "add a.txt back", map[string]string{"a.txt": "branch\n"})
	})
	head := b.Spec.Head
	w.Branch("external", synced)
	w.Git("rm", "--quiet", "--end-of-options", "a.txt")
	e := w.Commit("external deletes a.txt")
	w.PushRef(downstream + "c/x")
	o := &observed{Object: kube.Meta(b.Name, nil)}
	o.Namespace = "default"
	o.Status.Diverged = &gitk8s.Divergence{Commit: e, Ref: downstream + "c/x"}
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the branch rewound since it last synced at " + gitk8s.Short(synced) + ", and the branch with replays of the commits of the external repository's c/x doesn't have every change that the external repository's c/x made, so the check leaves the divergence for a person"
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "branch" {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestLeavesACopyOfARemovedCommit(t *testing.T) {
	// rebase copies synced's commit, which adds s.txt on top of base, onto
	// another commit on top of the current one, and reword copies the
	// current commit with another message. Each returns the copy.
	rebase := func(w *gittest.Work, synced string) string {
		commit(w, "other edit", map[string]string{"m.txt": "other\n"})
		w.Git("cherry-pick", "--end-of-options", synced)
		return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	}
	reword := func(w *gittest.Work) string {
		w.Git("commit", "--quiet", "--amend", "--message=reworded")
		return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	}
	for _, tc := range []struct {
		name string
		// sides returns c/x's head and the external head. One side
		// removes synced's commit, and the other copies it.
		sides func(w *gittest.Work, base, synced string) (head, external string)
		// merge says that c/x's head is a merge, which has no replay.
		merge bool
	}{{
		name: "when the branch rebased it",
		sides: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("copy", base)
			return rebase(w, synced), base
		},
	}, {
		name: "when the branch reworded it",
		sides: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("copy", synced)
			return reword(w), base
		},
	}, {
		name: "when the branch reworded it and merged the external head",
		sides: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("external", base)
			e := commit(w, "external edit", map[string]string{"d.txt": "external\n"})
			w.Branch("copy", synced)
			reword(w)
			w.Git("merge", "--quiet", "--no-edit", "--end-of-options", e)
			return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD"), e
		},
		merge: true,
	}, {
		name: "when the external repository reworded it",
		sides: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("copy", synced)
			return base, reword(w)
		},
	}, {
		name: "when the external repository rebased it",
		sides: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("copy", base)
			e := rebase(w, synced)
			w.Branch("c/x", base)
			return commit(w, "branch edit", map[string]string{"c.txt": "branch\n"}), e
		},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, base, synced := rewound(t, srv, func(*gittest.Work, *Branch) {})
			head, e := tc.sides(w, base, synced)
			w.Branch("c/x", head)
			w.Push("c/x")
			b.Spec.Head = head
			w.Branch("external", e)
			w.PushRef(downstream + "c/x")
			o := &observed{Object: kube.Meta(b.Name, nil)}
			o.Namespace = "default"
			o.Status.Diverged = &gitk8s.Divergence{Commit: e, Ref: downstream + "c/x"}
			syncedAt(w, o, "c/x", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			why := "the replays of the branch's commits onto the external repository's c/x don't have every change that both sides made"
			if tc.merge {
				why = "commit " + gitk8s.Short(head) + " of the branch is a merge, which has no replay"
			}
			want := "the branch and the external repository's c/x both rewound since they last synced at " + gitk8s.Short(synced) + ", and " + why + ", so the check leaves the divergence for a person"
			if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "both" {
				t.Errorf("result = %+v, want Failed with %q", res, want)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestLeavesAReplayThatUndoesAReset(t *testing.T) {
	for _, tc := range []struct {
		name string
		// synced is what the commit where the sides synced changes, and
		// branch is what the branch changes on top of it.
		synced, branch map[string]string
		// conflict is the file that conflicts when the check replays the
		// branch onto the external head.
		conflict string
		// resolved is the agent's resolution, or nil if git resolves the
		// conflict, and want says how the replay resolved it.
		resolved *agent.File
		want     string
	}{{
		name:     "that git's union driver resolved",
		synced:   map[string]string{"go.sum": "a v1\nb v1\n"},
		branch:   map[string]string{"go.sum": "a v1\nc v1\n"},
		conflict: "go.sum",
		want:     "replaying the branch onto the external repository's c/x conflicts in go.sum, which git merged with its union driver",
	}, {
		name:     "that the agent resolved",
		synced:   map[string]string{"a.txt": "one\nsynced\nthree\n"},
		branch:   map[string]string{"a.txt": "one\nbranch\nthree\n"},
		conflict: "a.txt",
		resolved: &agent.File{Path: "a.txt", Mode: "100644", Content: []byte("one\nbranch\nthree\n")},
		want:     "the agent resolved the conflicts in a.txt",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w, base := setup(t, srv, map[string]string{"b.txt": "main\n"}, tc.synced)
			synced := b.Spec.Head
			b.Spec.Head = commit(w, "branch edit", tc.branch)
			w.Push("c/x")
			if tc.resolved != nil {
				withJobs(t, finish(t, w, resolution(*tc.resolved)))
			}
			// The external repository resets c/x to base, which undoes the
			// commit where the sides synced.
			w.Branch("external", base)
			w.PushRef(downstream + "c/x")
			o := &observed{Object: kube.Meta(b.Name, nil)}
			o.Namespace = "default"
			o.Status.Diverged = &gitk8s.Divergence{Commit: base, Ref: downstream + "c/x"}
			syncedAt(w, o, "c/x", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			want := "replaying commit " + gitk8s.Short(b.Spec.Head) + " of the branch conflicts in " + tc.conflict + "; " + tc.want +
				", but the replay doesn't keep every change that the external repository's c/x at " + gitk8s.Short(base) +
				" made since they last synced at " + gitk8s.Short(synced) + ", so the check leaves the divergence for a person"
			if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want {
				t.Errorf("result = %+v, want Failed with %q", res, want)
			}
			if got := srv.Heads(t, "app")["c/x"]; got != b.Spec.Head {
				t.Errorf("c/x moved to %s", got)
			}
		})
	}
}

func TestReplaysABranchThatMergedTheRewoundExternalHead(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {
		commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	})
	// The external repository drops synced's commit, and c/x merges the
	// external head, so c/x contains both heads and still has s.txt.
	e, o := diverge(w, b.Name, "c/x", base, map[string]string{"d.txt": "external\n"})
	syncedAt(w, o, "c/x", synced)
	w.Branch("c/x", b.Spec.Head)
	w.Git("merge", "--quiet", "--no-edit", "--end-of-options", e)
	b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Push("c/x")
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	if res.State != gitk8s.Fixed || res.Outputs["rewound"] != "external" || !strings.Contains(res.Message, "is a merge, which has no replay") {
		t.Fatalf("result = %+v, want Fixed with the branch replayed as one commit", res)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replay %s", got, fix)
	}
	if got := files(w, fix); got != "a.txt\nc.txt\nd.txt\ngo.sum" {
		t.Errorf("files = %q, want c.txt and d.txt, and not s.txt, which the external repository removed", got)
	}
}

func TestPassesWhenTheRewoundExternalHeadKeepsTheBranchsChanges(t *testing.T) {
	srv := gittest.NewServer(t, "")
	// c/x drops synced's commit, and the external repository drops it too
	// and builds on c/x's head.
	b, w, base, synced := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	w.Branch("c/x", base)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	w.Push("c/x")
	head := b.Spec.Head
	e, o := diverge(w, b.Name, "c/x", head, map[string]string{"d.txt": "external\n"})
	syncedAt(w, o, "c/x", synced)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the external repository's c/x at " + gitk8s.Short(e) + " keeps every change that the branch made since they last synced at " + gitk8s.Short(synced)
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || res.Message != want || res.Outputs["rewound"] != "both" {
		t.Errorf("result = %+v, want Passed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestReplaysTheExternalCommitsWhenBothSidesRewound(t *testing.T) {
	srv := gittest.NewServer(t, "")
	// The sides synced at s2, on top of s1. c/x drops both, and the
	// external repository drops only s2.
	b, w, base, s1 := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	w.Branch("synced", s1)
	s2 := commit(w, "synced 2", map[string]string{"s2.txt": "synced\n"})
	w.Branch("c/x", base)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"c.txt": "branch\n"})
	w.Push("c/x")
	e, o := diverge(w, b.Name, "c/x", s1, map[string]string{"d.txt": "external\n"})
	syncedAt(w, o, "c/x", s2)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	fix := res.Outputs["fix"]
	want := "the branch rewound since it last synced at " + gitk8s.Short(s2) + "; replayed the commits that the external repository's c/x added since then onto it; pushed " + gitk8s.Short(fix)
	if res.State != gitk8s.Fixed || res.Message != want || res.Outputs["rewound"] != "both" {
		t.Fatalf("result = %+v, want Fixed with %q", res, want)
	}
	if got := w.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the replay %s", got, fix)
	}
	if got := w.Git("log", "--format=%s", "--end-of-options", b.Spec.Head+".."+fix); got != "external edit" {
		t.Errorf("c/x's commits on top of its head = %q, want the replay of %s", got, gitk8s.Short(e))
	}
	if got := files(w, fix); got != "a.txt\nc.txt\nd.txt\ngo.sum" {
		t.Errorf("files = %q, want neither s.txt, which c/x removed, nor s2.txt, which both sides removed", got)
	}
}

func TestLeavesADivergenceInWhichBothSidesRewoundAndAReplayConflicts(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, base, s1 := rewound(t, srv, func(w *gittest.Work, _ *Branch) {})
	w.Branch("synced", s1)
	s2 := commit(w, "synced 2", map[string]string{"s2.txt": "synced\n"})
	w.Branch("c/x", s1)
	b.Spec.Head = commit(w, "branch edit", map[string]string{"a.txt": "one\nbranch\nthree\n"})
	w.Push("c/x")
	head := b.Spec.Head
	_, o := diverge(w, b.Name, "c/x", base, map[string]string{"a.txt": "one\nexternal\nthree\n"})
	syncedAt(w, o, "c/x", s2)
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the branch and the external repository's c/x both rewound since they last synced at " + gitk8s.Short(s2) + ", and replaying commit " + gitk8s.Short(head) + " of the branch conflicts in a.txt, so the check leaves the divergence for a person"
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["rewound"] != "both" {
		t.Errorf("result = %+v, want Failed with %q", res, want)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

// parent pushes main and returns its view, with the external repository's
// head of main on the downstream ref: base with a.txt, then mainFiles on
// main and externalFiles on the external head.
func parent(t *testing.T, srv *gittest.Server, mainFiles, externalFiles map[string]string) (b *Branch, w *gittest.Work, e string, o *observed) {
	w = srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	base := w.Commit("base")
	head := commit(w, "main edit", mainFiles)
	w.Push("main")
	e, o = diverge(w, "app-main", "main", base, externalFiles)
	b = &Branch{Object: kube.Meta("app-main", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: head}
	return b, w, e, o
}

func TestPushesABranchThatResolvesADivergedParent(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w, e, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
	head := b.Spec.Head
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	pushed := srv.Heads(t, "app")["resolve/main"]
	if res.State != gitk8s.Running || pushed == "" || !strings.HasPrefix(res.Message, "pushed "+gitk8s.Short(pushed)+" to resolve/main") {
		t.Fatalf("result = %+v and resolve/main at %q, want Running after a push", res, pushed)
	}
	if res.Commit != head || res.Outputs["diverged"] != e || res.Outputs["branch"] != "resolve/main" {
		t.Errorf("result = %+v", res)
	}
	if got := srv.Heads(t, "app")["main"]; got != head {
		t.Errorf("main moved to %s; only resolve/main may change", got)
	}
	w.Fetch("resolve/main")
	if got := w.Git("log", "-1", "--format=%P %T", "--end-of-options", pushed); got != e+" "+w.Git("rev-parse", "--verify", "--end-of-options", e+"^{tree}") {
		t.Errorf("resolve/main's parent and tree = %s, want the external head's", got)
	}
	if msg := w.Git("log", "-1", "--format=%B", "--end-of-options", pushed); !strings.HasPrefix(msg, "Resolve the divergence of main from the external repository\n") || !strings.Contains(msg, e) || !strings.HasSuffix(msg, git.FixerTrailer+": conflicts") {
		t.Errorf("resolve/main's message = %q", msg)
	}

	child := &Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", "resolve/main"), nil)}
	child.Namespace = "default"
	child.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "resolve/main", Head: pushed, Parent: "main", ParentHead: head}
	if _, err := reconcile(t, srv, b, rules, o, child); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || !strings.HasPrefix(res.Message, "waiting for resolve/main, which holds the external repository's head") {
		t.Errorf("result = %+v, want Running while resolve/main lands", res)
	}
	if got := srv.Heads(t, "app")["resolve/main"]; got != pushed {
		t.Errorf("resolve/main moved to %s while it lands", got)
	}

	// resolve/main lands with main merged in.
	w.Branch("main", pushed)
	w.Git("merge", "--quiet", "--no-edit", "-s", "ours", "--end-of-options", head)
	b.Spec.Head = w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Push("main")
	if _, err := reconcile(t, srv, b, rules, o, child); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.HasPrefix(res.Message, "main contains the external repository's head") {
		t.Errorf("result after resolve/main lands = %+v, want Passed", res)
	}
}

func TestReusesALandedResolveBranch(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, e, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
	w.Branch("old", b.Spec.Head+"~1")
	w.Push("resolve/main")
	old := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	pushed := srv.Heads(t, "app")["resolve/main"]
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || pushed == old {
		t.Fatalf("result = %+v and resolve/main at %s, want a push over the landed branch", res, pushed)
	}
	w.Fetch("resolve/main")
	if got := w.Git("log", "-1", "--format=%P", "--end-of-options", pushed); got != e {
		t.Errorf("resolve/main's parent = %s, want the external head %s", got, e)
	}
}

func TestWaitsForAnUnlandedResolveBranch(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
	w.Branch("other", b.Spec.Head)
	commit(w, "other work", map[string]string{"b.txt": "other\n"})
	w.Push("resolve/main")
	other := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || !strings.HasPrefix(res.Message, "waiting for resolve/main to land on main or be deleted") {
		t.Errorf("result = %+v, want Running while resolve/main holds other work", res)
	}
	if got := srv.Heads(t, "app")["resolve/main"]; got != other {
		t.Errorf("resolve/main moved to %s", got)
	}
}

func TestLeavesADivergedParent(t *testing.T) {
	limited := []gitk8s.BranchRule{
		{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "conflicts", MayPush: true}}}},
		{Match: "**", Parent: "main", Merge: &gitk8s.MergePolicy{MaxAutomatedCommits: new(int32(0))}},
	}
	for _, tc := range []struct {
		name  string
		rules []gitk8s.BranchRule
		edit  func(o *observed)
		want  string
	}{{
		name: "when the policy doesn't let it push",
		rules: []gitk8s.BranchRule{
			{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "conflicts"}}}},
			{Match: "**", Parent: "main"},
		},
		want: "and the policy doesn't let this check push resolve/main to resolve it",
	}, {
		name: "without a rule that gives resolve/main the parent main",
		rules: []gitk8s.BranchRule{
			{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "conflicts", MayPush: true}}}},
			{Match: "c/**", Parent: "main"},
		},
		want: "add a rule that gives resolve/main the parent main, so that this check can resolve the divergence there",
	}, {
		name: "with a rule that gives resolve/main another parent",
		rules: []gitk8s.BranchRule{
			{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "conflicts", MayPush: true}}}},
			{Match: "resolve/**", Parent: "release"},
			{Match: "**", Parent: "main"},
		},
		want: "add a rule that gives resolve/main the parent main, so that this check can resolve the divergence there",
	}, {
		name:  "when resolve/main would have too many automated commits",
		rules: limited,
		want:  "which has 0 automated commits, so resolve/main would have more than the limit of 0",
	}, {
		name:  "with an invalid commit",
		rules: rules,
		edit:  func(o *observed) { o.Status.Diverged.Commit = "main" },
		want:  `status.diverged.commit is "main", which isn't a commit ID`,
	}, {
		name:  "with an invalid ref",
		rules: rules,
		edit:  func(o *observed) { o.Status.Diverged.Ref = "main" },
		want:  `status.diverged.ref is "main", but the mirror keeps the external repository's main at refs/git-k8s/downstream/heads/main`,
	}, {
		name:  "when the external repository deleted it",
		rules: rules,
		edit:  func(o *observed) { *o.Status.Diverged = gitk8s.Divergence{Base: strings.Repeat("a", 40)} },
		want:  "the external repository deleted main, which changed in git-k8s since they last synced at aaaaaaaaaaaa; push main to the external repository again",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, _, _, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
			if tc.edit != nil {
				tc.edit(o)
			}
			if _, err := reconcile(t, srv, b, tc.rules, o); err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, tc.want) {
				t.Errorf("result = %+v, want Failed with %q", res, tc.want)
			}
			if _, ok := srv.Heads(t, "app")["resolve/main"]; ok {
				t.Error("pushed resolve/main")
			}
		})
	}
}

func TestLimitsAResolveBranchByItsOwnRule(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _, _, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
	// The check's commit lands on resolve/main, which allows the default
	// number of automated commits, so main's limit doesn't apply.
	limited := []gitk8s.BranchRule{
		{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "conflicts", MayPush: true}}, MaxAutomatedCommits: new(int32(0))}},
		{Match: "**", Parent: "main"},
	}
	if _, err := reconcile(t, srv, b, limited, o); err != nil {
		t.Fatal(err)
	}
	pushed := srv.Heads(t, "app")["resolve/main"]
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || pushed == "" || !strings.HasPrefix(res.Message, "pushed "+gitk8s.Short(pushed)+" to resolve/main") {
		t.Errorf("result = %+v and resolve/main at %q, want Running after a push", res, pushed)
	}
}

func TestHandlesARewoundParent(t *testing.T) {
	for _, tc := range []struct {
		name string
		// heads makes main's head and the external repository's head on
		// top of base, which has a.txt, or synced, which adds s.txt.
		heads          func(w *gittest.Work, base, synced string) (head, e string)
		state, rewound string
		// want is the message, with {head}, {e}, and {synced} for those
		// commits.
		want string
	}{{
		name: "when the external repository rewound",
		heads: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("main", synced)
			head := commit(w, "main edit", map[string]string{"a.txt": "main\n"})
			w.Branch("external", base)
			return head, commit(w, "external edit", map[string]string{"b.txt": "external\n"})
		},
		state: gitk8s.Failed, rewound: "external",
		want: "the external repository rewound main since it last synced with git-k8s at {synced}, and the merge controller moves main only to a commit that contains its head, so only the external repository can resolve the divergence: push a head there that replays each commit that landed on main since {synced} unchanged, or that contains main's head {head}",
	}, {
		name: "when main rewound",
		heads: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("main", base)
			head := commit(w, "main edit", map[string]string{"a.txt": "main\n"})
			w.Branch("external", synced)
			return head, commit(w, "external edit", map[string]string{"b.txt": "external\n"})
		},
		state: gitk8s.Failed, rewound: "branch",
		want: "main rewound in git-k8s since it last synced with the external repository at {synced}; replay the commits that the external repository added since then onto main's head {head}, and push the result to the external repository with a lease on its head {e}",
	}, {
		name: "after the external repository replays main's commits",
		heads: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("main", synced)
			head := commit(w, "main edit", map[string]string{"a.txt": "main\n"})
			w.Branch("external", base)
			return head, commit(w, "main edit", map[string]string{"a.txt": "main\n"})
		},
		state: gitk8s.Passed, rewound: "external",
		want: "the external repository's head {e} keeps every change that main made since they last synced at {synced}",
	}, {
		name: "after main replays the external repository's commits",
		heads: func(w *gittest.Work, base, synced string) (string, string) {
			w.Branch("main", base)
			head := commit(w, "external edit", map[string]string{"b.txt": "external\n"})
			w.Branch("external", synced)
			return head, commit(w, "external edit", map[string]string{"b.txt": "external\n"})
		},
		state: gitk8s.Passed, rewound: "branch",
		want: "main keeps every change that the external repository's head {e} made since they last synced at {synced}",
	}, {
		name: "when both rewound",
		heads: func(w *gittest.Work, base, _ string) (string, string) {
			w.Branch("main", base)
			head := commit(w, "main edit", map[string]string{"a.txt": "main\n"})
			w.Branch("external", base)
			return head, commit(w, "external edit", map[string]string{"b.txt": "external\n"})
		},
		state: gitk8s.Failed, rewound: "both",
		want: "main rewound both in git-k8s and in the external repository since they last synced at {synced}, so the check leaves the divergence for a person",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			w := srv.NewWork(t, "app")
			w.Write("a.txt", "one\n")
			base := w.Commit("base")
			synced := commit(w, "synced", map[string]string{"s.txt": "synced\n"})
			head, e := tc.heads(w, base, synced)
			w.PushRef(downstream + "main")
			w.Branch("main", head)
			w.Push("main")
			b := &Branch{Object: kube.Meta("app-main", nil)}
			b.Namespace = "default"
			b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: head}
			o := &observed{Object: kube.Meta("app-main", nil)}
			o.Namespace = "default"
			o.Status.Diverged = &gitk8s.Divergence{Commit: e, Ref: downstream + "main"}
			syncedAt(w, o, "main", synced)
			if _, err := reconcile(t, srv, b, rules, o); err != nil {
				t.Fatal(err)
			}
			want := strings.NewReplacer("{head}", gitk8s.Short(head), "{e}", gitk8s.Short(e), "{synced}", gitk8s.Short(synced)).Replace(tc.want)
			if res := b.Status.Checks.Result; res.State != tc.state || res.Message != want || res.Outputs["rewound"] != tc.rewound {
				t.Errorf("result = %+v, want %s with %q", res, tc.state, want)
			}
			heads := srv.Heads(t, "app")
			if _, ok := heads["resolve/main"]; ok {
				t.Error("pushed resolve/main, which would bring back the commits that the rewind removed")
			}
			if heads["main"] != head {
				t.Errorf("main moved to %s", heads["main"])
			}
		})
	}
}

func TestPassesWhenTheExternalHeadContainsTheParent(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w, _, _ := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
	e, o := diverge(w, b.Name, "main", b.Spec.Head, map[string]string{"b.txt": "external\n"})
	if _, err := reconcile(t, srv, b, rules, o); err != nil {
		t.Fatal(err)
	}
	want := "the external repository's head " + gitk8s.Short(e) + " already contains main's head"
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || res.Message != want {
		t.Errorf("result = %+v, want Passed with %q", res, want)
	}
	if _, ok := srv.Heads(t, "app")["resolve/main"]; ok {
		t.Error("pushed resolve/main")
	}
}

func TestIgnoresParentsWithNothingToResolve(t *testing.T) {
	for _, tc := range []struct {
		name     string
		rules    []gitk8s.BranchRule
		diverged bool
	}{
		{name: "without a divergence", rules: rules},
		{name: "without the check in the policy", rules: []gitk8s.BranchRule{{Match: "**", Parent: "main"}}, diverged: true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, _, _, o := parent(t, srv, map[string]string{"a.txt": "main\n"}, map[string]string{"a.txt": "external\n"})
			b.Status.Checks.Result = &gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Running}
			var world []any
			if tc.diverged {
				world = append(world, o)
			}
			if _, err := reconcile(t, srv, b, tc.rules, world...); err != nil {
				t.Fatal(err)
			}
			if res := b.Status.Checks.Result; res != nil {
				t.Errorf("result = %+v, want none", res)
			}
			if _, ok := srv.Heads(t, "app")["resolve/main"]; ok {
				t.Error("pushed resolve/main")
			}
		})
	}
}

func TestParsesUnionPatterns(t *testing.T) {
	var p patterns
	if err := p.Set(" go.sum, **/go.sum ,"); err != nil || p.String() != "go.sum,**/go.sum" {
		t.Errorf("Set = %v, patterns = %q", err, p.String())
	}
	if err := p.Set(""); err != nil || len(p) != 0 {
		t.Errorf("Set(\"\") = %v, patterns = %q, want none", err, p.String())
	}
	if err := p.Set("go.sum,!vendor"); err == nil {
		t.Error("Set accepted a negated pattern")
	}
}

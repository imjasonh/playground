package main

import (
	"bytes"
	"context"
	"fmt"
	"maps"
	"path"
	"strconv"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

const instructions = `Resolve each conflict so that the result keeps what both sides meant to change. Read the commits of both sides, the branch's change, the code around each conflict, and the code that it uses. When both sides change the same lines for different reasons, combine the changes. Never drop one side's change to make a conflict go away. Change only the files that conflict, and leave no conflict markers in them.

Answer fail, and leave the files as they are, when you can't tell how to keep both sides' changes, such as when the two sides contradict each other. A wrong resolution is worse than none, because a person resolves the conflicts that you leave. You can't build or run the code here; other checks build and test the merge after you.`

// divergedInstructions come first in a divergence's instructions, because
// the agent's prompt names the same branch on both sides of the merge.
const divergedInstructions = `The merged branch is this branch as the external repository holds it. The branch changed both in git-k8s and in the external repository since they last synced, and this merge joins the two.

`

var runner = &agent.Runner{Name: "conflicts"}

// tools leave out delete, because a resolution keeps every file that
// conflicts.
var tools = []string{"read", "grep", "glob", "ls", "edit"}

// runJob starts or follows an agent's run. Tests replace it.
var runJob = func(ctx context.Context, job *agent.Job, st *agent.JobState) agent.JobStatus {
	return runner.RunJob(ctx, job, st)
}

// job is the agent's job that resolves the conflicts of merging t into the
// branch's head, with base as the merge base.
func (t target) job(in *checks.Input, base string) *agent.Job {
	task := agent.Task{Instructions: instructions, Edit: true}
	if t.diverged {
		task.Instructions = divergedInstructions + instructions
	}
	return &agent.Job{
		Name:        in.Meta.Name,
		Namespace:   in.Meta.Namespace,
		URL:         in.Repository.Spec.URL,
		Credentials: in.Repository.Spec.SecretRef,
		Checkout: agent.Checkout{
			Branch: in.Spec.Branch,
			Head:   in.Spec.Head,
			Parent: in.Spec.Parent,
			Base:   base,
			Merge:  &agent.Ref{Name: t.ref, Commit: t.commit, DisplayName: t.name},
			Union:  union,
		},
		Task:    task,
		Tools:   tools,
		MaxRuns: in.Spec.Merge.MaxRuns(),
	}
}

// follow follows the agent's run that the previous result started on the
// branch's head to merge the same kind of target, and reports whether it
// did. It comes before any git work, because kube deletes the run's Pod
// after a reconcile that doesn't declare it. The run keeps merging the
// commit that it started with, so that a parent that keeps moving doesn't
// start a new run each time. The check starts over instead when -union
// changed, because git might then resolve every conflict, or when the run
// waits for a commit that t already has. Then it updates the runs in
// outputs, which the new run counts from.
func follow(ctx context.Context, in *checks.Input, t target, outputs map[string]string) (checks.Verdict, bool) {
	prev := in.Previous
	if prev == nil || prev.State != gitk8s.Running || prev.Commit != in.Spec.Head || prev.Outputs["pod"] == "" ||
		(prev.Outputs["diverged"] != "") != t.diverged || !isCommit(prev.Outputs["merge"]) || !isCommit(prev.Outputs["base"]) ||
		prev.Outputs["union"] != union.String() {
		return checks.Verdict{}, false
	}
	pinned, base := t, prev.Outputs["base"]
	pinned.commit = prev.Outputs["merge"]
	st := jobState(prev.Outputs)
	s := runJob(ctx, pinned.job(in, base), st)
	if s.Moved && pinned.commit != t.commit {
		// RunJob gave back the run whose Pod found the branch moved.
		outputs["runs"] = strconv.Itoa(st.Runs)
		return checks.Verdict{}, false
	}
	v := report(ctx, in, pinned, base, st, s)
	for _, k := range []string{"diverged", "conflicts"} {
		if prev.Outputs[k] != "" {
			v.Outputs[k] = prev.Outputs[k]
		}
	}
	return v, true
}

// startAgent starts the agent's run that resolves the conflicts that git
// leaves when it merges t into the branch's head. bases are the merge
// bases, and list names the files that conflict.
func startAgent(ctx context.Context, in *checks.Input, repo *git.Repo, t target, bases []string, list string, outputs map[string]string) checks.Verdict {
	if len(bases) > 1 {
		return checks.Fail("the branch and %s have %d merge bases, so their conflicts have no one base for the agent to compare", t.name, len(bases))
	}
	base := bases[0]
	tree, conflicts, err := repo.Merge(ctx, in.Spec.Head, t.commit, git.MergeOptions{Base: base, Union: union})
	if err != nil {
		return retry(ctx, "merging %s: %v", t.name, err)
	}
	why, err := unresolvable(ctx, repo, in.Spec.Head, t, tree, conflicts)
	switch {
	case err != nil:
		return retry(ctx, "reading the files that conflict: %v", err)
	case why != "":
		return checks.Fail("%s", why)
	}
	st := &agent.JobState{}
	st.Runs, _ = strconv.Atoi(outputs["runs"])
	s := runJob(ctx, t.job(in, base), st)
	if !s.Done && st.Pod == "" {
		s.Message = fmt.Sprintf("merging %s conflicts in %s; %s", t.name, list, s.Message)
	}
	return report(ctx, in, t, base, st, s)
}

// unresolvable says why the agent can't resolve the conflicts of merging t
// into head, or returns "" if it can. tree is the merge, and conflicts are
// the files that conflict in it.
func unresolvable(ctx context.Context, repo *git.Repo, head string, t target, tree string, conflicts []git.Conflict) (string, error) {
	if len(conflicts) > agent.MaxFiles {
		return fmt.Sprintf("merging %s has conflicts in %d files, more than the agent can change", t.name, len(conflicts)), nil
	}
	size := 0
	for _, c := range conflicts {
		if path.Base(c.Path) == ".cursorignore" {
			return fmt.Sprintf("merging %s conflicts on %s, which the agent can't see, because its work tree leaves out .cursorignore files", t.name, c.Path), nil
		}
		if c.Ours == nil || c.Theirs == nil || !textMode(c.Ours.Mode) || !textMode(c.Theirs.Mode) {
			return fmt.Sprintf("merging %s conflicts on %s, which isn't a file on both sides, so the agent can't resolve it", t.name, c.Path), nil
		}
		b, err := repo.ReadBlob(ctx, tree+":"+c.Path)
		if err != nil {
			return "", err
		}
		if !hasLine(b, "<<<<<<< "+head) {
			return fmt.Sprintf("merging %s conflicts on %s, which git can't mark with conflict markers, such as a binary file", t.name, c.Path), nil
		}
		size += len(b)
	}
	if size > agent.MaxFileBytes {
		return fmt.Sprintf("the files that conflict hold more than %d MiB, more than the agent can change", agent.MaxFileBytes>>20), nil
	}
	return "", nil
}

// report turns how the agent's run that merges t, with base as the merge
// base, stands into the check's verdict. When the agent resolves the
// conflicts, the verdict's fix is the merge that its files resolve.
func report(ctx context.Context, in *checks.Input, t target, base string, st *agent.JobState, s agent.JobStatus) checks.Verdict {
	running := func(format string, args ...any) checks.Verdict {
		return checks.Verdict{State: gitk8s.Running, Message: fmt.Sprintf(format, args...), Outputs: runOutputs(t, base, st)}
	}
	if !s.Done {
		return running("%s", s.Message)
	}
	o := map[string]string{"runs": strconv.Itoa(st.Runs), "merge": t.commit}
	if st.Pod != "" {
		o["pod"] = st.Pod
	}
	res := s.Result
	if res == nil {
		v := checks.Fail("%s", s.Message)
		if s.Failed != nil {
			maps.Copy(o, agent.UsageOutputs(s.Failed))
		}
		v.Outputs = o
		return v
	}
	var v checks.Verdict
	if res.Verdict == agent.Fail {
		v = checks.Fail("the agent couldn't resolve the conflicts: %s", s.Message)
	} else {
		repo, err := targetRepo(ctx, in, t)
		if err != nil {
			// The Pod still serves the result, and RunJob declared it in
			// this reconcile. Leaving the run undone in the outputs makes
			// the next reconcile follow the Pod and fetch the result again,
			// instead of RunJob reporting the run as done without it.
			st.Done = false
			kube.RequeueAfter(ctx, 30*time.Second)
			return running("fetching the branch and %s to commit the agent's resolution: %v", t.name, err)
		}
		fix, paths, err := commitResolution(ctx, in, repo, t, base, res)
		if err != nil {
			v = checks.Fail("can't commit the agent's resolution: %v", err)
		} else {
			v = checks.Fail("the agent resolved the conflicts in %s", strings.Join(paths, ", "))
			v.Fix = fix
		}
	}
	maps.Copy(o, agent.UsageOutputs(res))
	o["summary"] = res.Summary
	v.Outputs = o
	return v
}

// runOutputs hold what the next reconcile needs to follow the agent's run
// that merges t, with base as the merge base.
func runOutputs(t target, base string, st *agent.JobState) map[string]string {
	o := map[string]string{"runs": strconv.Itoa(st.Runs), "merge": t.commit}
	if st.Pod == "" {
		return o
	}
	o["pod"], o["attempt"], o["base"] = st.Pod, strconv.Itoa(st.Attempt), base
	if st.UID != "" {
		o["podUID"] = st.UID
	}
	if st.Refunded != "" {
		o["refunded"] = st.Refunded
	}
	if st.Done {
		o["done"] = "true"
	}
	if len(union) > 0 {
		o["union"] = union.String()
	}
	return o
}

// jobState reads the state of the agent's run from the outputs that
// runOutputs wrote.
func jobState(outputs map[string]string) *agent.JobState {
	st := &agent.JobState{Pod: outputs["pod"], UID: outputs["podUID"], Refunded: outputs["refunded"], Done: outputs["done"] == "true"}
	st.Runs, _ = strconv.Atoi(outputs["runs"])
	st.Attempt, _ = strconv.Atoi(outputs["attempt"])
	return st
}

// commitResolution makes the merge of t into the branch's head that the
// agent's files resolve, after checking that the agent's Pod made the same
// merge, and that the files change only files that conflict and leave no
// conflict markers. It returns the merge and the files that conflicted.
func commitResolution(ctx context.Context, in *checks.Input, repo *git.Repo, t target, base string, res *agent.Result) (string, []string, error) {
	head := in.Spec.Head
	tree, conflicts, err := repo.Merge(ctx, head, t.commit, git.MergeOptions{Base: base, Union: union})
	if err != nil {
		return "", nil, err
	}
	if tree != res.MergeTree {
		return "", nil, fmt.Errorf("the agent resolved a merge with the tree %s, but the check's merge has the tree %s", res.MergeTree, tree)
	}
	byPath := make(map[string]git.Conflict, len(conflicts))
	for _, c := range conflicts {
		byPath[c.Path] = c
	}
	for _, f := range res.Files {
		c, ok := byPath[f.Path]
		switch {
		case !ok:
			return "", nil, fmt.Errorf("the agent changed %s, which doesn't conflict", f.Path)
		case f.Deleted:
			return "", nil, fmt.Errorf("the agent deleted %s", f.Path)
		case (c.Ours == nil || f.Mode != c.Ours.Mode) && (c.Theirs == nil || f.Mode != c.Theirs.Mode):
			return "", nil, fmt.Errorf("the agent gave %s the mode %s, which it has on neither side", f.Path, f.Mode)
		}
	}
	resolved, err := agent.ApplyFiles(ctx, repo, tree, res.Files)
	if err != nil {
		return "", nil, err
	}
	paths := make([]string, len(conflicts))
	for i, c := range conflicts {
		paths[i] = c.Path
		if err := checkResolved(ctx, repo, resolved, c, "<<<<<<< "+head, "||||||| "+base, ">>>>>>> "+t.commit); err != nil {
			return "", nil, err
		}
	}
	body := strings.Join(paths, "\n")
	if res.Summary != "" {
		body = res.Summary + "\n\n" + body
	}
	fix, err := mergeCommit(ctx, in, repo, t, resolved, body)
	return fix, paths, err
}

// checkResolved returns an error if a file that conflicted, as it is in
// tree, holds a line that starts with one of the merge's conflict marker
// labels, or more lines that look like conflict markers than its two sides
// hold together.
func checkResolved(ctx context.Context, repo *git.Repo, tree string, c git.Conflict, labels ...string) error {
	if c.Ours == nil || c.Theirs == nil {
		return fmt.Errorf("%s isn't a file on both sides", c.Path)
	}
	got, err := repo.ReadBlob(ctx, tree+":"+c.Path)
	if err != nil {
		return err
	}
	for _, label := range labels {
		if hasLine(got, label) {
			return fmt.Errorf("conflict markers remain in %s", c.Path)
		}
	}
	var sides [len(markerPrefixes)]int
	for _, e := range []*git.TreeEntry{c.Ours, c.Theirs} {
		b, err := repo.ReadBlob(ctx, e.SHA)
		if err != nil {
			return err
		}
		for i, n := range markerLines(b) {
			sides[i] += n
		}
	}
	for i, n := range markerLines(got) {
		if n > sides[i] {
			return fmt.Errorf("%s has more lines that start with %s than its two sides, so conflict markers remain", c.Path, markerPrefixes[i])
		}
	}
	return nil
}

// markerPrefixes start the marker lines of a conflict in the diff3 style.
var markerPrefixes = [...]string{"<<<<<<<", "|||||||", "=======", ">>>>>>>"}

// markerLines counts the lines of b that start like each conflict marker.
func markerLines(b []byte) [len(markerPrefixes)]int {
	var n [len(markerPrefixes)]int
	for line := range bytes.Lines(b) {
		for i, p := range markerPrefixes {
			rest, ok := bytes.CutPrefix(line, []byte(p))
			if ok && (len(rest) == 0 || rest[0] == ' ' || rest[0] == '\n' || rest[0] == '\r') {
				n[i]++
			}
		}
	}
	return n
}

// hasLine reports whether a line of b starts with prefix.
func hasLine(b []byte, prefix string) bool {
	for line := range bytes.Lines(b) {
		if bytes.HasPrefix(line, []byte(prefix)) {
			return true
		}
	}
	return false
}

func textMode(mode string) bool { return mode == "100644" || mode == "100755" }

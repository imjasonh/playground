// Command check-conflicts resolves the conflicts that keep branches from
// landing.
//
// The conflicts check handles two kinds of conflict:
//
//   - Merging a branch's parent into it conflicts, so the base check can't
//     keep the branch up to date. The conflicts check pushes a merge of the
//     parent that resolves the conflicts.
//   - A branch changed both in the in-cluster mirror and in the external
//     repository that the mirror syncs, so the mirror overwrites neither,
//     and the branch's status.diverged holds the external repository's
//     head. The conflicts check pushes a merge of that head, which the
//     mirror then syncs to the external repository.
//
// Git resolves what it can first: paths that match -union, such as go.sum,
// merge with git's union driver, which keeps the lines of both sides. When
// other conflicts remain and -agent-image is set, an agent in a sandboxed
// Pod resolves them, as in check-review. The check never pushes a merge
// that picks one side of a conflict or still holds conflict markers. When
// neither git nor the agent resolves the conflicts, the check fails and
// leaves the branch as it is.
//
// A merge pushed to a branch without a parent would skip the branch's
// merge gate. So when one diverges, the check pushes the external
// repository's head, with a commit that says why, to the branch
// resolve/BRANCH instead, and that branch lands through the gate like any
// other.
package main

import (
	"cmp"
	"context"
	"flag"
	"fmt"
	"log/slog"
	"maps"
	"path/filepath"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"conflicts,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// observed is a GitBranch's divergence. It's a type of its own because kube
// applies the status of Branch, and the check mustn't write
// status.diverged.
type observed struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Status      struct {
		Diverged *gitk8s.Divergence `json:"diverged,omitempty"`
	} `json:"status,omitzero"`
}

// divergence returns a GitBranch's divergence from the external
// repository, or nil.
func divergence(ctx context.Context, meta *kube.ObjectMeta) *gitk8s.Divergence {
	if o := kube.Get[observed](ctx, meta.Namespace, meta.Name); o != nil {
		return o.Status.Diverged
	}
	return nil
}

const instructions = `Resolve each conflict so that the result keeps what both sides meant to change. Read each side's commits and diff, the code around each conflict, and the code that it uses. When both sides change the same lines for different reasons, combine the changes. Never drop one side's change to make a conflict go away.

Answer fail, and leave the files as they are, when you can't tell how to keep both sides' changes, such as when the two sides contradict each other. A wrong resolution is worse than none, because a person resolves the conflicts that you leave. You can't build or run the code here; other checks build and test the merge after you.`

var runner = &agent.Runner{Name: "conflicts"}

var union = patterns{"go.sum"}

var check = checks.Check{Name: "conflicts", UsesParent: true, Remote: credentials.Remote, Stale: stale, Run: run}

// stale reports whether the previous result is for another merge than the
// one that the branch needs now: the branch diverged or stopped diverging,
// or the agent's run finished merging a head of the parent that has since
// moved.
func stale(ctx context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool {
	diverged := ""
	if d := divergence(ctx, meta); d != nil {
		diverged = d.Commit
	}
	if diverged != previous.Outputs["diverged"] {
		return true
	}
	merged := previous.Outputs["merge"]
	return diverged == "" && merged != "" && merged != spec.ParentHead
}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	outputs := map[string]string{}
	if prev := in.Previous; prev != nil && prev.Outputs["runs"] != "" {
		// The agent counts the branch's runs for maxAgentRuns in this
		// output, so every result keeps it.
		outputs["runs"] = prev.Outputs["runs"]
	}
	v := resolveBranch(ctx, in, outputs)
	maps.Copy(outputs, v.Outputs)
	v.Outputs = outputs
	return v, nil
}

// retry reports a failure that can pass, such as a fetch that failed, and
// runs the check again later. The check doesn't return errors, because the
// framework reports an error without the outputs.
func retry(ctx context.Context, format string, args ...any) checks.Verdict {
	kube.RequeueAfter(ctx, 30*time.Second)
	return checks.Verdict{State: gitk8s.Running, Message: fmt.Sprintf(format, args...)}
}

// target is a commit to merge into a branch.
type target struct {
	commit string
	// ref is where commit is on the remote.
	ref  string
	name string
	// diverged says that commit is the external repository's head, which
	// the branch takes a merge of even without conflicts, because nothing
	// else merges it.
	diverged bool
}

func (t target) task() agent.Task {
	return agent.Task{Instructions: instructions, Merge: &agent.Merge{Commit: t.commit, Ref: t.ref, Name: t.name, Union: union}}
}

// resolveBranch resolves a branch's divergence from the external
// repository, or else the conflicts of merging its parent into it.
func resolveBranch(ctx context.Context, in *checks.Input, outputs map[string]string) checks.Verdict {
	head := in.Spec.Head
	t := target{commit: in.Spec.ParentHead, ref: "refs/heads/" + in.Spec.Parent, name: in.Spec.Parent}
	d := divergence(ctx, in.Meta)
	if d != nil {
		outputs["diverged"] = d.Commit
		if err := validate(d); err != nil {
			return checks.Fail("%v", err)
		}
		t = target{commit: d.Commit, ref: d.Ref, name: "the external repository's " + in.Spec.Branch, diverged: true}
	}
	if v, ok := follow(ctx, in, t); ok {
		return v
	}
	repo, err := in.Repo(ctx)
	if err != nil {
		return retry(ctx, "fetching the branch: %v", err)
	}
	if d != nil {
		remote, err := in.Remote(ctx)
		if err != nil {
			return retry(ctx, "fetching %s: %v", d.Ref, err)
		}
		if err := fetchCommit(ctx, repo, remote, d.Commit, d.Ref); err != nil {
			return retry(ctx, "fetching %s: %v", d.Ref, err)
		}
	}
	switch ok, err := repo.IsAncestor(ctx, t.commit, head); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return checks.Pass("contains %s at %s", t.name, gitk8s.Short(t.commit))
	}
	// A merge of a commit that already contains the branch would change
	// nothing.
	switch ok, err := repo.IsAncestor(ctx, head, t.commit); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return checks.Pass("%s at %s already contains the branch's head", t.name, gitk8s.Short(t.commit))
	}
	return resolve(ctx, in, repo, t, outputs)
}

// follow follows the agent's run that the previous result started on the
// branch's head to merge the same kind of target, and reports whether it
// did. It comes before any git work, because kube deletes the run's Pod
// after a reconcile that doesn't declare it. The run keeps merging the
// commit that it started with, so that a parent that keeps moving doesn't
// start a new run each time.
func follow(ctx context.Context, in *checks.Input, t target) (checks.Verdict, bool) {
	prev := in.Previous
	if prev == nil || prev.State != gitk8s.Running || prev.Commit != in.Spec.Head || prev.Outputs["pod"] == "" ||
		(prev.Outputs["diverged"] != "") != t.diverged || !isCommit(prev.Outputs["merge"]) {
		return checks.Verdict{}, false
	}
	t.commit = prev.Outputs["merge"]
	v, _ := runner.Run(ctx, in, t.task())
	if v.Outputs["pod"] == "" {
		// The run can't go on as it started, such as after -union changed,
		// so the check starts over.
		return checks.Verdict{}, false
	}
	for _, k := range []string{"diverged", "merge", "conflicts"} {
		if prev.Outputs[k] != "" {
			v.Outputs[k] = prev.Outputs[k]
		}
	}
	return v, true
}

// resolve merges t into the branch's head. It returns a verdict whose fix
// is a merge that git resolved, or the verdict of the agent's run that
// resolves the conflicts that git leaves.
func resolve(ctx context.Context, in *checks.Input, repo *git.Repo, t target, outputs map[string]string) checks.Verdict {
	head := in.Spec.Head
	outputs["merge"] = t.commit
	bases, err := repo.MergeBases(ctx, head, t.commit)
	if err != nil {
		return retry(ctx, "finding the merge base with %s: %v", t.name, err)
	}
	if len(bases) == 0 {
		return checks.Fail("the branch shares no history with %s, so git can't merge them", t.name)
	}
	tree, conflicts, err := repo.Merge(ctx, head, t.commit, git.MergeOptions{})
	if err != nil {
		return retry(ctx, "merging %s: %v", t.name, err)
	}
	if len(conflicts) == 0 {
		if !t.diverged {
			return checks.Pass("merging %s at %s has no conflicts to resolve", t.name, gitk8s.Short(t.commit))
		}
		return fix(ctx, in, repo, t, tree, "", checks.Fail("the branch diverged from %s at %s, which merges without conflicts", t.name, gitk8s.Short(t.commit)))
	}
	paths := make([]string, len(conflicts))
	for i, c := range conflicts {
		paths[i] = c.Path
	}
	list := strings.Join(paths, ", ")
	outputs["conflicts"] = strings.Join(paths, ",")
	if len(union) > 0 {
		tree, rest, err := repo.Merge(ctx, head, t.commit, git.MergeOptions{Union: union})
		if err != nil {
			return retry(ctx, "merging %s: %v", t.name, err)
		}
		if len(rest) == 0 {
			body := "Git merged these files with its union driver, which keeps the lines of both sides:\n\n" + strings.Join(paths, "\n")
			return fix(ctx, in, repo, t, tree, body, checks.Fail("merging %s conflicts in %s, which git merged with its union driver", t.name, list))
		}
	}
	switch {
	case runner.Image == "":
		return checks.Fail("merging %s conflicts in %s; git can't resolve them, and the check runs no agent without -agent-image", t.name, list)
	case !in.Policy.MayPush:
		return checks.Fail("merging %s conflicts in %s; the policy doesn't let this check push a resolution, so it runs no agent", t.name, list)
	}
	base, err := in.MergeBase(ctx)
	if err != nil {
		return retry(ctx, "finding the merge base with %s: %v", in.Spec.Parent, err)
	}
	n, err := repo.CountFixerCommits(ctx, base, head)
	if err != nil {
		return retry(ctx, "counting automated commits: %v", err)
	}
	if limit := in.Spec.Merge.MaxCommits(); n >= limit {
		return checks.Fail("merging %s conflicts in %s; not running an agent because the branch already has %d automated commits, the limit", t.name, list, n)
	}
	v, _ := runner.Run(ctx, in, t.task())
	return v
}

// fix returns v with a merge of t into the branch's head, with tree, as its
// fix.
func fix(ctx context.Context, in *checks.Input, repo *git.Repo, t target, tree, body string, v checks.Verdict) checks.Verdict {
	hc, err := repo.Commit(ctx, in.Spec.Head)
	if err != nil {
		return retry(ctx, "reading the branch's head: %v", err)
	}
	tc, err := repo.Commit(ctx, t.commit)
	if err != nil {
		return retry(ctx, "reading %s: %v", t.name, err)
	}
	msg := fmt.Sprintf("Merge %s into %s\n\n", t.name, in.Spec.Branch)
	if body != "" {
		msg += body + "\n\n"
	}
	msg += git.FixerTrailer + ": conflicts\n"
	v.Fix, err = repo.CommitTree(ctx, tree, []string{in.Spec.Head, t.commit}, msg, in.Identity, max(hc.Time, tc.Time))
	if err != nil {
		return retry(ctx, "committing the merge of %s: %v", t.name, err)
	}
	return v
}

// fetchCommit fetches ref from remote unless repo already has commit, and
// then checks that it has commit.
func fetchCommit(ctx context.Context, repo *git.Repo, remote git.Remote, commit, ref string) error {
	if ok, err := repo.HasCommit(ctx, commit); err != nil || ok {
		return err
	}
	if _, err := repo.FetchRef(ctx, remote, ref); err != nil {
		return err
	}
	if ok, err := repo.HasCommit(ctx, commit); err != nil || !ok {
		return cmp.Or(err, fmt.Errorf("fetched %s but don't have %s", ref, gitk8s.Short(commit)))
	}
	return nil
}

// validate returns an error if d can't be a divergence that the core
// program wrote.
func validate(d *gitk8s.Divergence) error {
	switch {
	case !isCommit(d.Commit):
		return fmt.Errorf("status.diverged.commit is %q, which isn't a commit ID", d.Commit)
	case !strings.HasPrefix(d.Ref, "refs/"):
		// The ref reaches git in the agent's Pod, which would read a ref
		// that starts with a dash as an option.
		return fmt.Errorf("status.diverged.ref is %q, which isn't a full ref name", d.Ref)
	}
	return nil
}

// isCommit reports whether s is a full SHA-1 or SHA-256 commit ID.
func isCommit(s string) bool {
	if len(s) != 40 && len(s) != 64 {
		return false
	}
	return strings.Trim(s, "0123456789abcdef") == ""
}

// resolvePrefix starts the name of the branch that resolves the divergence
// of a branch without a parent.
const resolvePrefix = "resolve/"

// reconciler runs the conflicts check on branches with a parent, and
// resolves the divergence of branches without one, which the checks
// framework doesn't run checks on.
type reconciler struct {
	check kube.Reconciler[Branch]
	cfg   *checks.Config
	cache *gitk8s.Cache
}

func newReconciler(cfg *checks.Config) *reconciler {
	return &reconciler{
		check: checks.NewReconciler[Branch](check, cfg),
		cfg:   cfg,
		// The checks framework keeps its own Cache in cfg.CacheDir, and two
		// Caches don't lock each other's repositories.
		cache: &gitk8s.Cache{Git: &cfg.Git, Dir: filepath.Join(cfg.CacheDir, ".parents")},
	}
}

func (r *reconciler) Reconcile(ctx context.Context, b *Branch) error {
	if b.Spec.Parent != "" {
		return r.check.Reconcile(ctx, b)
	}
	return r.resolveParent(ctx, b)
}

// resolveParent resolves the divergence of a branch without a parent. It
// pushes a commit on top of the external repository's head to the branch
// resolve/BRANCH, which the repository's rules must give the parent
// BRANCH. That branch lands through BRANCH's merge gate once BRANCH is
// merged into it, by the base check, or by the conflicts check when the
// merge conflicts.
func (r *reconciler) resolveParent(ctx context.Context, b *Branch) error {
	result := &b.Status.Checks.Result
	d := divergence(ctx, &b.ObjectMeta)
	if d == nil {
		*result = nil
		return nil
	}
	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	if repo == nil {
		return fmt.Errorf("GitRepository %s/%s doesn't exist", b.Namespace, b.Spec.Repository)
	}
	rule := gitk8s.FindRule(repo.Spec.Branches, b.Spec.Branch)
	var policy *gitk8s.CheckPolicy
	if rule != nil {
		policy = rule.Merge.Check("conflicts")
	}
	if policy == nil {
		*result = nil
		return nil
	}
	branch, child := b.Spec.Branch, resolvePrefix+b.Spec.Branch
	res := &gitk8s.CheckResult{Commit: b.Spec.Head, Outputs: map[string]string{"diverged": d.Commit, "branch": child}}
	*result = res
	report := func(state, format string, args ...any) error {
		res.State, res.Message = state, truncate(fmt.Sprintf(format, args...))
		return nil
	}
	fail := func(err error) error {
		res.State, res.Message = gitk8s.Error, truncate(err.Error())
		return err
	}
	if err := validate(d); err != nil {
		return report(gitk8s.Failed, "%v", err)
	}
	switch cr := gitk8s.FindRule(repo.Spec.Branches, child); {
	case !policy.MayPush:
		return report(gitk8s.Failed, "%s diverged from the external repository at %s, and the policy doesn't let this check push %s to resolve it", branch, gitk8s.Short(d.Commit), child)
	case cr == nil || cr.Parent != branch:
		return report(gitk8s.Failed, "%s diverged from the external repository at %s; add a rule that gives %s the parent %s, so that this check can resolve the divergence there", branch, gitk8s.Short(d.Commit), child, branch)
	}

	local, unlock, err := r.cache.Open(ctx, repo)
	if err != nil {
		return fail(err)
	}
	defer unlock()
	remote, err := credentials.Remote(ctx, repo)
	if err != nil {
		return fail(err)
	}
	heads, err := r.cfg.Git.LsRemote(ctx, remote)
	if err != nil {
		return fail(err)
	}
	head, childHead := b.Spec.Head, heads[child]
	fetch := []string{branch}
	if childHead != "" {
		fetch = append(fetch, child)
	}
	if err := local.Fetch(ctx, remote, fetch...); err != nil {
		return fail(err)
	}
	if err := fetchCommit(ctx, local, remote, d.Commit, d.Ref); err != nil {
		return fail(err)
	}
	if ok, err := local.HasCommit(ctx, head); err != nil || !ok {
		return fail(cmp.Or(err, fmt.Errorf("fetched %s but don't have %s; waiting for the repository controller to list it again", branch, gitk8s.Short(head))))
	}
	contained, err := local.IsAncestor(ctx, d.Commit, head)
	if err != nil {
		return fail(err)
	}
	if contained {
		return report(gitk8s.Passed, "%s contains the external repository's head %s", branch, gitk8s.Short(d.Commit))
	}
	// Reading the child's GitBranch runs this again when the child changes
	// or is deleted.
	kube.Get[Branch](ctx, b.Namespace, gitk8s.BranchObjectName(b.Spec.Repository, child))
	if childHead != "" {
		holds, err := local.IsAncestor(ctx, d.Commit, childHead)
		if err != nil {
			return fail(err)
		}
		if holds {
			return report(gitk8s.Running, "waiting for %s, which holds the external repository's head %s, to land on %s", child, gitk8s.Short(d.Commit), branch)
		}
		landed, err := local.IsAncestor(ctx, childHead, head)
		if err != nil {
			return fail(err)
		}
		if !landed {
			return report(gitk8s.Running, "waiting for %s to land on %s or be deleted, so that this check can push the external repository's head %s to it", child, branch, gitk8s.Short(d.Commit))
		}
	}

	base, err := local.MergeBase(ctx, d.Commit, head)
	if err != nil {
		return fail(err)
	}
	n, err := local.CountFixerCommits(ctx, base, d.Commit)
	if err != nil {
		return fail(err)
	}
	if limit := rule.Merge.MaxCommits(); n >= limit {
		return report(gitk8s.Failed, "%s diverged from the external repository at %s, which has %d automated commits, so %s would have more than the limit of %d", branch, gitk8s.Short(d.Commit), n, child, limit)
	}
	c, err := local.Commit(ctx, d.Commit)
	if err != nil {
		return fail(err)
	}
	msg := fmt.Sprintf("Resolve the divergence of %s from the external repository\n\n"+
		"%s changed both in the in-cluster mirror and in the external repository\n"+
		"since they last synced. This branch starts at the external repository's\n"+
		"head, %s, and lands on %s through its merge gate after %s\n"+
		"is merged into it.\n\n%s: conflicts\n", branch, branch, d.Commit, branch, branch, git.FixerTrailer)
	commit, err := local.CommitTree(ctx, c.Tree, []string{d.Commit}, msg, r.cfg.Identity, c.Time)
	if err != nil {
		return fail(err)
	}
	if err := local.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + child, New: commit, Old: childHead}); err != nil {
		return fail(fmt.Errorf("pushing %s to %s: %w", gitk8s.Short(commit), child, err))
	}
	slog.Info("pushed a branch that resolves a divergence", "namespace", b.Namespace, "branch", child, "parent", branch, "commit", gitk8s.Short(commit))
	return report(gitk8s.Running, "pushed %s to %s, which lands on %s with the external repository's head %s", gitk8s.Short(commit), child, branch, gitk8s.Short(d.Commit))
}

// truncate keeps a message to the size that the checks framework allows.
func truncate(s string) string {
	if len(s) > 1024 {
		return s[:1021] + "..."
	}
	return s
}

// patterns is a flag that holds comma-separated path patterns.
type patterns []string

func (p *patterns) String() string { return strings.Join(*p, ",") }

func (p *patterns) Set(s string) error {
	var list []string
	for f := range strings.SplitSeq(s, ",") {
		if f = strings.TrimSpace(f); f != "" {
			list = append(list, f)
		}
	}
	if _, err := git.UnionAttributes(list); err != nil {
		return err
	}
	*p = list
	return nil
}

func main() {
	cfg := &checks.Config{}
	cfg.AddFlags(flag.CommandLine)
	runner.AddFlags(flag.CommandLine)
	flag.CommandLine.Lookup("agent-image").Usage = "image that runs the agent, built from agent/runner/Dockerfile; without it, the check resolves only what git can"
	flag.Var(&union, "union", "comma-separated path patterns, in the gitattributes format, whose conflicts git resolves by keeping the lines of both sides")
	kube.Main(kube.For[Branch](newReconciler(cfg), kube.Named("check-conflicts")))
}

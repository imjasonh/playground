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
//     mirror then syncs to the external repository. When a side rewound
//     since the sides last synced, a merge brings back the commits that
//     the rewind removed, so the check replays the other side's commits
//     onto the rewound side's head instead. When the external repository
//     deleted the branch, the check fails and leaves the branch for a
//     person.
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
// other. When a side of such a branch rewound, resolve/BRANCH would bring
// back the commits that the rewind removed, so the check pushes nothing,
// and says how to resolve the divergence. A branch without a parent takes
// no check results, so the check reports on it with events instead.
//
// The check and its agent Pods fetch from the mirror, which keeps the
// external repository's heads and the heads where the two sides last
// synced under refs/git-k8s/, and the check pushes to the mirror. The
// mirror lets a check create no branches, so the core program's
// -branch-prefix gives the check's service account the prefix resolve/.
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
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/git-k8s/signing"
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

// observed is a GitBranch's divergence. It's a type of its own because a
// check's view of a GitBranch holds only the spec and the check's result.
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

var union = patterns{"go.sum"}

// The agent reads the subjects of the branch's commits, and a replay keeps
// their authors and messages, so the check isn't FilesOnly.
var check = checks.Check{Name: "conflicts", UsesParent: true, Remote: mirror.Remote, SigningKey: signing.Key, Stale: stale, Run: run}

// stale reports whether the previous result is for another merge than the
// one that the branch needs now: the branch diverged or stopped diverging,
// the external repository's head or the head where the two sides last
// synced moved, or the agent's run finished merging a head of the parent
// that has since moved.
func stale(ctx context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool {
	d := divergence(ctx, meta)
	var diverged, synced string
	if d != nil {
		diverged, synced = d.Commit, d.Base
	}
	if diverged != previous.Notes["diverged"] || synced != previous.Notes["synced"] {
		return true
	}
	merged := previous.Notes["merge"]
	return d == nil && merged != "" && merged != spec.ParentHead
}

// record holds the outputs and notes that the check records as it works
// toward a verdict. run adds the verdict's own outputs and notes to them.
type record struct{ outputs, notes map[string]string }

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	rec := record{outputs: map[string]string{}, notes: map[string]string{}}
	if prev := in.Previous; prev != nil {
		// RunJob counts the branch's runs for maxAgentRuns in the agent's
		// state, so every result keeps them.
		if runs := readState(prev.Notes).Runs; runs != 0 {
			rec.notes = stateNotes(&agent.JobState{Runs: runs})
		}
	}
	v := resolveBranch(ctx, in, rec)
	maps.Copy(rec.outputs, v.Outputs)
	maps.Copy(rec.notes, v.Notes)
	v.Outputs, v.Notes, v.Message = rec.outputs, rec.notes, shorten(v.Message)
	return v, nil
}

// retry reports a failure that can pass, such as a fetch that failed, as
// Running instead of Error, and runs the check again later.
func retry(ctx context.Context, format string, args ...any) checks.Verdict {
	kube.RequeueAfter(ctx, 30*time.Second)
	return checks.Verdict{State: gitk8s.Running, Message: fmt.Sprintf(format, args...)}
}

// target is a commit to merge into a branch.
type target struct {
	commit string
	// ref is the full name of a ref on the remote that holds commit, and
	// name names it in messages and in the agent's prompt.
	ref, name string
	// diverged says that commit is the external repository's head, which
	// the branch takes a merge of even without conflicts, because nothing
	// else merges it.
	diverged bool
	// synced is the head where the branch last synced with the external
	// repository, if commit is the external repository's head and they
	// synced.
	synced string
	// replay says that the external repository rewound since synced, so
	// instead of a merge of commit, the check makes one commit on top of
	// commit that replays the branch's changes since synced.
	replay bool
}

// action names what the check does with t, for messages.
func (t target) action() string {
	if t.replay {
		return "replaying the branch onto " + t.name
	}
	return "merging " + t.name
}

// resolveBranch resolves a branch's divergence from the external
// repository, or else the conflicts of merging its parent into it. When
// neither side of a divergence rewound since the sides last synced, a
// head that contains both heads keeps both sides' changes, so the check
// merges the external repository's head.
func resolveBranch(ctx context.Context, in *checks.Input, rec record) checks.Verdict {
	head := in.Spec.Head
	t := target{commit: in.Spec.ParentHead, ref: "refs/heads/" + in.Spec.Parent, name: in.Spec.Parent}
	if d := divergence(ctx, in.Meta); d != nil {
		recordDivergence(d, rec.notes)
		if err := validate(d, in.Spec.Branch); err != nil {
			return checks.Fail("%v", err)
		}
		if d.Commit == "" {
			return checks.Fail("%s", deletion(in.Spec.Branch, d))
		}
		t = target{commit: d.Commit, ref: d.Ref, name: "the external repository's " + in.Spec.Branch, diverged: true, synced: d.Base}
	}
	if v, ok := follow(ctx, in, t, rec); ok {
		return v
	}
	repo, err := targetRepo(ctx, in, t)
	if err != nil {
		return retry(ctx, "fetching the branch and %s: %v", t.name, err)
	}
	if t.synced != "" {
		switch rewound, err := rewinds(ctx, repo, head, t.commit, t.synced); {
		case err != nil:
			return retry(ctx, "%v", err)
		case rewound != "":
			rec.notes["rewound"] = rewound
			return resolveRewind(ctx, in, repo, t, rewound, rec)
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
	return resolve(ctx, in, repo, t, rec)
}

// resolve merges t into the branch's head, or, if t.replay is set,
// replays the branch's changes since t.synced onto t's commit as one
// commit. It returns a verdict whose fix is a commit that git resolved,
// or the verdict of the agent's run that resolves the conflicts that git
// leaves.
func resolve(ctx context.Context, in *checks.Input, repo *git.Repo, t target, rec record) checks.Verdict {
	head := in.Spec.Head
	rec.notes["merge"] = t.commit
	var o git.MergeOptions
	var bases []string
	if t.replay {
		o.Base, bases = t.synced, []string{t.synced}
	} else {
		var err error
		if bases, err = repo.MergeBases(ctx, head, t.commit); err != nil {
			return retry(ctx, "finding the merge base with %s: %v", t.name, err)
		}
		if len(bases) == 0 {
			return checks.Fail("the branch shares no history with %s, so git can't merge them", t.name)
		}
	}
	tree, conflicts, err := repo.Merge(ctx, head, t.commit, o)
	if err != nil {
		return retry(ctx, "%s: %v", t.action(), err)
	}
	if len(conflicts) == 0 {
		switch {
		case t.replay:
			return fix(ctx, in, repo, t, tree, "", checks.Fail("replayed the branch's commits since %s onto %s at %s as one commit", gitk8s.Short(t.synced), t.name, gitk8s.Short(t.commit)))
		case !t.diverged:
			return checks.Pass("merging %s at %s has no conflicts to resolve", t.name, gitk8s.Short(t.commit))
		}
		return fix(ctx, in, repo, t, tree, "", checks.Fail("the branch diverged from %s at %s, which merges without conflicts", t.name, gitk8s.Short(t.commit)))
	}
	paths := make([]string, len(conflicts))
	for i, c := range conflicts {
		paths[i] = c.Path
	}
	list := strings.Join(paths, ", ")
	rec.outputs["conflicts"] = strings.Join(paths, ",")
	if len(union) > 0 {
		o.Union = union
		tree, rest, err := repo.Merge(ctx, head, t.commit, o)
		if err != nil {
			return retry(ctx, "%s: %v", t.action(), err)
		}
		if len(rest) == 0 {
			body := "Git merged these files with its union driver, which keeps the lines of both sides:\n\n" + strings.Join(paths, "\n")
			return fix(ctx, in, repo, t, tree, body, checks.Fail("%s conflicts in %s, which git merged with its union driver", t.action(), list))
		}
	}
	switch {
	case runner.Image == "":
		return checks.Fail("%s conflicts in %s; git can't resolve them, and the check runs no agent without -agent-image", t.action(), list)
	case !in.Policy.MayPush:
		return checks.Fail("%s conflicts in %s; the policy doesn't let this check push a resolution, so it runs no agent", t.action(), list)
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
		return checks.Fail("%s conflicts in %s; not running an agent because the branch already has %d automated commits, the limit", t.action(), list, n)
	}
	return startAgent(ctx, in, repo, t, bases, list, rec.notes)
}

// fix returns v with the commit that mergeCommit makes of tree as its fix,
// unless keepsExternal turns it into a failure.
func fix(ctx context.Context, in *checks.Input, repo *git.Repo, t target, tree, body string, v checks.Verdict) checks.Verdict {
	var err error
	if v.Fix, err = mergeCommit(ctx, in, repo, t, tree, body); err != nil {
		return retry(ctx, "committing the result of %s: %v", t.action(), err)
	}
	if v, err = keepsExternal(ctx, repo, t, v); err != nil {
		return retry(ctx, "comparing the result of %s with %s: %v", t.action(), t.name, err)
	}
	return v
}

// mergeCommit commits tree as a merge of t into the branch's head, or, if
// t.replay is set, as a commit on top of t's commit that replays the
// branch's changes since t.synced, with body in the message. The message
// ends with the fixer trailer and then the trailers, each set to conflicts.
func mergeCommit(ctx context.Context, in *checks.Input, repo *git.Repo, t target, tree, body string, trailers ...string) (string, error) {
	hc, err := repo.Commit(ctx, in.Spec.Head)
	if err != nil {
		return "", err
	}
	tc, err := repo.Commit(ctx, t.commit)
	if err != nil {
		return "", err
	}
	branch := in.Spec.Branch
	parents := []string{in.Spec.Head, t.commit}
	msg := fmt.Sprintf("Merge %s into %s\n\n", t.name, branch)
	if t.replay {
		parents = []string{t.commit}
		msg = fmt.Sprintf("Replay %s onto %s\n\n"+
			"The external repository rewound %s since it last synced with git-k8s,\n"+
			"so this commit replays the changes that %s made since then onto the\n"+
			"external repository's head, as one commit:\n\n%s..%s\n\n", branch, t.name, branch, branch, t.synced, in.Spec.Head)
	}
	if body != "" {
		msg += body + "\n\n"
	}
	msg += git.FixerTrailer + ": conflicts\n"
	for _, k := range trailers {
		msg += k + ": conflicts\n"
	}
	return in.CommitTree(ctx, tree, parents, msg, max(hc.Time, tc.Time))
}

// targetRepo returns the branch's repository with t's commit, which it
// fetches from t's ref when t isn't the parent's head, which the checks
// framework fetches, and with the head where the branch last synced, if
// t has one.
func targetRepo(ctx context.Context, in *checks.Input, t target) (*git.Repo, error) {
	repo, err := in.Repo(ctx)
	if err != nil || !t.diverged {
		return repo, err
	}
	remote, err := in.Remote(ctx)
	if err != nil {
		return nil, err
	}
	if err := fetchCommit(ctx, repo, remote, t.commit, t.ref); err != nil || t.synced == "" {
		return repo, err
	}
	return repo, fetchCommit(ctx, repo, remote, t.synced, syncedPrefix+in.Spec.Branch)
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

// recordDivergence records d in notes, so that stale can tell when it
// changes.
func recordDivergence(d *gitk8s.Divergence, notes map[string]string) {
	if d.Commit != "" {
		notes["diverged"] = d.Commit
	}
	if d.Base != "" {
		notes["synced"] = d.Base
	}
}

// downstreamPrefix starts the refs in the mirror that hold the external
// repository's heads.
const downstreamPrefix = "refs/git-k8s/downstream/heads/"

// validate returns an error if d can't be a divergence of branch that the
// core program wrote.
func validate(d *gitk8s.Divergence, branch string) error {
	deleted := d.Commit == "" && d.Ref == ""
	switch {
	case !deleted && !isCommit(d.Commit):
		return fmt.Errorf("status.diverged.commit is %q, which isn't a commit ID", d.Commit)
	case !deleted && d.Ref != downstreamPrefix+branch:
		// The check merges or replays whatever the ref holds, such as
		// another branch or a pull request's head on the external
		// repository, and the ref reaches git in the agent's Pod.
		return fmt.Errorf("status.diverged.ref is %q, but the mirror keeps the external repository's %s at %s", d.Ref, branch, downstreamPrefix+branch)
	case d.Base != "" && !isCommit(d.Base), deleted && d.Base == "":
		// The mirror pushes a branch that the external repository never
		// had, so only a branch that the two sides synced can diverge by
		// a deletion.
		return fmt.Errorf("status.diverged.base is %q, which isn't a commit ID", d.Base)
	}
	return nil
}

// deletion says why the check can't resolve the divergence d of branch, in
// which the external repository deleted the branch.
func deletion(branch string, d *gitk8s.Divergence) string {
	return fmt.Sprintf("the external repository deleted %s, which changed in git-k8s since they last synced at %s; push %s to the external repository again to keep its changes, or delete it in git-k8s to drop them",
		branch, gitk8s.Short(d.Base), branch)
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
// framework doesn't run checks on, and which take no check results.
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
	b.Status.Checks.Result = nil
	return r.resolveParent(ctx, b)
}

// resolveParent resolves the divergence of a branch without a parent. It
// pushes a commit on top of the external repository's head to the branch
// resolve/BRANCH, which the repository's rules must give the parent
// BRANCH. That branch lands through BRANCH's merge gate once BRANCH is
// merged into it, by the base check, or by the conflicts check when the
// merge conflicts. When a side rewound since the sides last synced,
// parentRewind decides instead.
//
// The branch takes no check results, so resolveParent records each outcome
// other than a push as a ResolvingDivergence event instead: a Warning when
// it fails, and Normal when it waits or passes.
func (r *reconciler) resolveParent(ctx context.Context, b *Branch) error {
	d := divergence(ctx, &b.ObjectMeta)
	if d == nil {
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
		return nil
	}
	branch, child := b.Spec.Branch, resolvePrefix+b.Spec.Branch
	report := func(state, format string, args ...any) error {
		eventType := kube.Normal
		if state == gitk8s.Failed {
			eventType = kube.Warning
		}
		kube.Eventf(ctx, eventType, "ResolvingDivergence", format, args...)
		return nil
	}
	fail := func(err error) error {
		kube.Eventf(ctx, kube.Warning, "ResolvingDivergence", "%s", err)
		return err
	}
	if err := validate(d, branch); err != nil {
		return report(gitk8s.Failed, "%v", err)
	}
	if d.Commit == "" {
		return report(gitk8s.Failed, "%s", deletion(branch, d))
	}

	local, unlock, err := r.cache.Open(ctx, repo)
	if err != nil {
		return fail(err)
	}
	defer unlock()
	remote, err := check.Remote(ctx, repo)
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
	if d.Base != "" {
		if err := fetchCommit(ctx, local, remote, d.Base, syncedPrefix+branch); err != nil {
			return fail(err)
		}
		rewound, err := rewinds(ctx, local, head, d.Commit, d.Base)
		if err != nil {
			return fail(err)
		}
		if rewound != "" {
			state, msg, err := parentRewind(ctx, local, branch, head, d, rewound)
			if err != nil {
				return fail(err)
			}
			return report(state, "%s", msg)
		}
	}
	contained, err := local.IsAncestor(ctx, d.Commit, head)
	if err != nil {
		return fail(err)
	}
	if contained {
		return report(gitk8s.Passed, "%s contains the external repository's head %s", branch, gitk8s.Short(d.Commit))
	}
	// The mirror moves the branch to an external head that contains it.
	switch ok, err := local.IsAncestor(ctx, head, d.Commit); {
	case err != nil:
		return fail(err)
	case ok:
		return report(gitk8s.Passed, "the external repository's head %s already contains %s's head", gitk8s.Short(d.Commit), branch)
	}
	cr := gitk8s.FindRule(repo.Spec.Branches, child)
	switch {
	case !policy.MayPush:
		return report(gitk8s.Failed, "%s diverged from the external repository at %s, and the policy doesn't let this check push %s to resolve it", branch, gitk8s.Short(d.Commit), child)
	case cr == nil || cr.Parent != branch:
		return report(gitk8s.Failed, "%s diverged from the external repository at %s; add a rule that gives %s the parent %s, so that this check can resolve the divergence there", branch, gitk8s.Short(d.Commit), child, branch)
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
	if limit := cr.Merge.MaxCommits(); n >= limit {
		return report(gitk8s.Failed, "%s diverged from the external repository at %s, which has %d automated commits, so %s would have more than the limit of %d", branch, gitk8s.Short(d.Commit), n, child, limit)
	}
	c, err := local.Commit(ctx, d.Commit)
	if err != nil {
		return fail(err)
	}
	key, err := signing.Key(ctx, repo)
	if err != nil {
		return fail(err)
	}
	msg := fmt.Sprintf("Resolve the divergence of %s from the external repository\n\n"+
		"%s changed both in the in-cluster mirror and in the external repository\n"+
		"since they last synced. This branch starts at the external repository's\n"+
		"head, %s, and lands on %s through its merge gate after %s\n"+
		"is merged into it.\n\n%s: conflicts\n", branch, branch, d.Commit, branch, branch, git.FixerTrailer)
	commit, err := local.CommitTree(ctx, c.Tree, []string{d.Commit}, msg, r.cfg.Identity, c.Time, key)
	if err != nil {
		return fail(err)
	}
	if err := local.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + child, New: commit, Old: childHead}); err != nil {
		return fail(fmt.Errorf("pushing %s to %s: %w", gitk8s.Short(commit), child, err))
	}
	slog.Info("pushed a branch that resolves a divergence", "namespace", b.Namespace, "branch", child, "parent", branch, "commit", gitk8s.Short(commit))
	kube.Eventf(ctx, kube.Normal, "PushedFix", "pushed %s to %s, which lands on %s with the external repository's head %s", gitk8s.Short(commit), child, branch, gitk8s.Short(d.Commit))
	return nil
}

// maxMessage leaves room in the checks framework's 1,024-byte messages for
// what it appends about a fix.
const maxMessage = 896

// shorten cuts s to at most maxMessage bytes, on a rune boundary.
func shorten(s string) string {
	if len(s) <= maxMessage {
		return s
	}
	i := maxMessage - len("...")
	for i > 0 && !utf8.RuneStart(s[i]) {
		i--
	}
	return s[:i] + "..."
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
	checks.RemoveLeftoverSigningKeys()
	kube.Main(checks.ForReconciler[Branch](check, cfg, newReconciler(cfg)))
}

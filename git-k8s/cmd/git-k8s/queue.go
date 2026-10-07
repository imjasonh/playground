package main

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"maps"
	"slices"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// queueEntry is a GitBranch as merge queues see it. It doesn't declare check
// results, so their changes don't reconcile a parent or the branches in its
// queue.
type queueEntry struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        struct {
		Branch string `json:"branch"`
		Parent string `json:"parent,omitempty"`
	} `json:"spec"`
	Status struct {
		Queued *gitk8s.Queued `json:"queued,omitempty"`
		Queue  []string       `json:"queue,omitempty"`
	} `json:"status,omitzero"`
}

// queues reports whether branches land on their parent through its merge
// queue, which they do when the base check may merge the parent into them.
func queues(policy *gitk8s.MergePolicy) bool {
	c := policy.Check("base")
	return c != nil && c.MayPush
}

// queue returns the branches in b's merge queue, front first. Branches keep
// their places, so the front stays the front until it leaves. Branches that
// join go to the back, in the order that they joined, then by name. Only a
// parent whose merge policy queues branches has a queue.
func queue(ctx context.Context, b *gitk8s.GitBranch) ([]string, error) {
	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	if repo == nil {
		return nil, nil
	}
	rule := gitk8s.FindRule(repo.Spec.Branches, b.Spec.Branch)
	isParent := func(r gitk8s.BranchRule) bool { return r.Parent == b.Spec.Branch }
	if rule == nil || !queues(rule.Merge) || !slices.ContainsFunc(repo.Spec.Branches, isParent) {
		return nil, nil
	}
	entries := kube.List[queueEntry](ctx, kube.InNamespace(b.Namespace),
		kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: b.Spec.Repository}))
	waiting := map[string]*gitk8s.Queued{}
	for _, e := range entries {
		if e.Spec.Parent == b.Spec.Branch && e.Status.Queued != nil {
			waiting[e.Spec.Branch] = e.Status.Queued
		}
	}
	// Only reconciles of b write its queue, one at a time, so each starts
	// from the queue that the last one wrote. The cache can lag that write,
	// and rebuilding an older queue could put another branch at the front
	// while the last front merges the parent in.
	last, err := kube.Fetch[queueEntry](ctx, b.Namespace, b.Name)
	if err != nil {
		// kube writes the status of a failed reconcile too, and the cached
		// queue can be older than the last one. Keep only its branches that
		// are still queued, so that one that left doesn't get its old place
		// back when it joins again.
		return slices.DeleteFunc(b.Status.Queue, func(branch string) bool { return waiting[branch] == nil }), err
	}
	var q []string
	if last != nil {
		for _, branch := range last.Status.Queue {
			if waiting[branch] != nil {
				q = append(q, branch)
				delete(waiting, branch)
			}
		}
	}
	joined := slices.SortedFunc(maps.Keys(waiting), func(x, y string) int {
		return cmp.Or(waiting[x].Since.Compare(waiting[y].Since), cmp.Compare(x, y))
	})
	return append(q, joined...), nil
}

// position returns b's place in its parent's queue, from 1 at the front or 0
// if the queue doesn't include b yet, and the queue's length.
func position(ctx context.Context, b *gitk8s.GitBranch) (int32, int) {
	parent := kube.Get[queueEntry](ctx, b.Namespace, gitk8s.BranchObjectName(b.Spec.Repository, b.Spec.Parent))
	if parent == nil {
		return 0, 0
	}
	return int32(slices.Index(parent.Status.Queue, b.Spec.Branch) + 1), len(parent.Status.Queue)
}

// queued lands b through its parent's queue. b joins the queue when its gate
// passes and the base check passes, which the base check does for a branch
// that's behind its parent but merges cleanly. b leaves the queue when it
// lands, when someone other than a check pushes to it, or when its checks
// finish without passing. At the front, b leaves as soon as it can't pass
// even if its unfinished checks do, so it doesn't hold up the branches
// behind it. It also leaves when a squash or rebase landing needs a person
// to rebase it, and then it doesn't join again until its spec changes.
// Otherwise, a branch that leaves joins again at the back. Only the branch
// at the front lands, after the base check merges the parent into it if
// it's behind. A squash or rebase landing that pushes its commits to b for
// the checks keeps b at the front while the checks run on them.
func (m *merger) queued(ctx context.Context, repo *gitk8s.Repository, b *gitk8s.GitBranch, q *gitk8s.Queued, checks map[string]gitk8s.GateCheck, results map[string]gitk8s.CheckResult, pass bool) error {
	spec := &b.Spec
	switch {
	case reported(b, gitk8s.MergeStateRewritten):
		// The checks see the rewritten commits once the repository
		// controller lists them. Until then, b's results are for its old
		// head, so b holds its place without landing.
		b.Status.Queued = q
		return nil
	case reported(b, gitk8s.MergeStateNeedsRebase):
		return nil
	}
	base := checks["base"]
	ready := pass && base.Passed
	if q != nil && q.Head != spec.Head {
		kept, err := m.fixedOnly(ctx, repo, b, q.Head)
		if err != nil {
			b.Status.Queued = q
			return err
		}
		if !kept {
			q = nil
		}
	}
	if q == nil && !ready {
		report(b, gitk8s.MergeStateWaitingForChecks, "%s", describe(spec.Merge, checks))
		return nil
	}
	pos, n := position(ctx, b)
	if q == nil && pos != 0 {
		// The parent reads b through another watch, so it can list b before
		// b's own cache has the write in which b joined. Only a b that the
		// API server has queued at its current head keeps its place.
		live, err := kube.Fetch[queueEntry](ctx, b.Namespace, b.Name)
		if err != nil {
			report(b, gitk8s.MergeStateQueued, "rejoining %s's queue at the back", spec.Parent)
			return fmt.Errorf("reading %s's place in %s's queue: %w", spec.Branch, spec.Parent, err)
		}
		if live != nil && live.Status.Queued != nil && live.Status.Queued.Head == spec.Head {
			q = live.Status.Queued
		}
	}
	switch {
	case q == nil && pos != 0:
		// b left, but the parent's queue still lists it, and joining now
		// would keep its old place.
		report(b, gitk8s.MergeStateQueued, "rejoining %s's queue at the back", spec.Parent)
		return nil
	case q == nil:
		q = &gitk8s.Queued{Since: time.Now().UTC().Truncate(time.Second)}
	case !ready && (settled(checks) || pos == 1 && !canPass(spec.Merge, checks)):
		report(b, gitk8s.MergeStateWaitingForChecks, "%s", describe(spec.Merge, checks))
		return nil
	}
	q.Head, q.Position = spec.Head, pos
	b.Status.Queued = q
	switch {
	case pos == 0:
		report(b, gitk8s.MergeStateQueued, "joining %s's queue", spec.Parent)
	case pos > 1:
		report(b, gitk8s.MergeStateQueued, "%d of %d in %s's queue", pos, n, spec.Parent)
	case !ready:
		report(b, gitk8s.MergeStateQueued, "first in %s's queue; %s", spec.Parent, describe(spec.Merge, checks))
	case base.Outputs["behind"] == "true":
		report(b, gitk8s.MergeStateQueued, "first in %s's queue; waiting for the base check to merge %s in", spec.Parent, spec.Parent)
	default:
		report(b, gitk8s.MergeStateQueued, "first in %s's queue", spec.Parent)
		if err := m.land(ctx, repo, b, results); err != nil {
			return err
		}
		switch b.Status.State {
		case gitk8s.MergeStateLanded, gitk8s.MergeStateNothingToLand, gitk8s.MergeStateNeedsRebase:
			b.Status.Queued = nil
		}
	}
	return nil
}

// landed reports whether this controller landed b at its current spec. Until
// the repository controller lists b again, b's checks still pass for its
// parent's old head, so b would otherwise join the queue again.
func landed(b *gitk8s.GitBranch) bool {
	return reported(b, gitk8s.MergeStateLanded)
}

// reported reports whether this controller set b's Landed condition to
// state at b's current spec. The spec changes when b or its parent moves.
func reported(b *gitk8s.GitBranch, state gitk8s.MergeState) bool {
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	return c != nil && c.Reason == string(state) && c.ObservedGeneration == b.Generation
}

// settled reports whether every check has passed or failed for the branch's
// current commits.
func settled(checks map[string]gitk8s.GateCheck) bool {
	for _, c := range checks {
		if c.State != gitk8s.Passed && c.State != gitk8s.Failed {
			return false
		}
	}
	return true
}

// canPass reports whether the base check and the gate can still pass if
// every check that hasn't passed or failed passes. A gate that fails to
// evaluate until those checks finish, such as one that reads an output that
// they haven't set, still can.
func canPass(policy *gitk8s.MergePolicy, checks map[string]gitk8s.GateCheck) bool {
	if checks["base"].State == gitk8s.Failed {
		return false
	}
	assumed := maps.Clone(checks)
	for name, c := range assumed {
		if c.State != gitk8s.Passed && c.State != gitk8s.Failed {
			assumed[name] = gitk8s.GateCheck{Passed: true, State: gitk8s.Passed, Outputs: c.Outputs}
		}
	}
	pass, err := evaluate(policy, assumed)
	return pass || err != nil
}

// fixedOnly reports whether checks pushed every commit that b gained since
// its head was since, such as the base check's merge of the parent, so that
// b keeps its place in the queue.
func (m *merger) fixedOnly(ctx context.Context, repo *gitk8s.Repository, b *gitk8s.GitBranch, since string) (bool, error) {
	if repo == nil {
		return false, fmt.Errorf("GitRepository %s/%s doesn't exist", b.Namespace, b.Spec.Repository)
	}
	local, err := m.mirror.Open(ctx, repo)
	if err != nil {
		return false, err
	}
	defer local.Close()
	if ok, err := local.HasCommit(ctx, b.Spec.Head); err != nil || !ok {
		return false, errors.Join(err, fmt.Errorf("the mirror doesn't have %s; waiting for the repository controller to list the branch again", gitk8s.Short(b.Spec.Head)))
	}
	// The copy prunes only commits that no ref has, so a missing earlier
	// head means that a push removed it.
	if ok, err := local.HasCommit(ctx, since); err != nil || !ok {
		return false, err
	}
	return local.OnlyFixerCommits(ctx, since, b.Spec.Head)
}

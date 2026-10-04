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
	// Only reconciles of b write its queue, one at a time, so each starts
	// from the queue that the last one wrote. The cache can lag that write,
	// and rebuilding an older queue could put another branch at the front
	// while the last front merges the parent in.
	last, err := kube.Fetch[queueEntry](ctx, b.Namespace, b.Name)
	if err != nil {
		return nil, err
	}
	entries := kube.List[queueEntry](ctx, kube.InNamespace(b.Namespace),
		kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: b.Spec.Repository}))
	waiting := map[string]*gitk8s.Queued{}
	for _, e := range entries {
		if e.Spec.Parent == b.Spec.Branch && e.Status.Queued != nil {
			waiting[e.Spec.Branch] = e.Status.Queued
		}
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
// finish without passing. Only the branch at the front lands, after the base
// check merges the parent into it if it's behind.
func (m *merger) queued(ctx context.Context, b *gitk8s.GitBranch, q *gitk8s.Queued, checks map[string]gitk8s.GateCheck, pass bool) error {
	spec := &b.Spec
	base := checks["base"]
	ready := pass && base.Passed
	if q != nil && q.Head != spec.Head {
		kept, err := m.fixedOnly(ctx, b, q.Head)
		if err != nil {
			b.Status.Queued = q
			return err
		}
		if !kept {
			q = nil
		}
	}
	if q != nil && !ready && settled(checks) {
		q = nil
	}
	if q == nil && !ready {
		report(b, reasonWaitingForChecks, false, "%s", describe(spec.Merge, checks))
		return nil
	}
	if q == nil {
		q = &gitk8s.Queued{Since: time.Now().UTC().Truncate(time.Second)}
	}
	pos, n := position(ctx, b)
	q.Head, q.Position = spec.Head, pos
	b.Status.Queued = q
	switch {
	case pos == 0:
		report(b, reasonQueued, false, "joining %s's queue", spec.Parent)
	case pos > 1:
		report(b, reasonQueued, false, "%d of %d in %s's queue", pos, n, spec.Parent)
	case !ready:
		report(b, reasonQueued, false, "first in %s's queue; %s", spec.Parent, describe(spec.Merge, checks))
	case base.Outputs["behind"] == "true":
		report(b, reasonQueued, false, "first in %s's queue; waiting for the base check to merge %s in", spec.Parent, spec.Parent)
	default:
		report(b, reasonQueued, false, "first in %s's queue", spec.Parent)
		if err := m.land(ctx, b); err != nil {
			return err
		}
		if c := kube.FindCondition(b.Status.Conditions, "Merged"); c.Status == kube.True {
			b.Status.Queued = nil
		}
	}
	return nil
}

// landed reports whether this controller landed b at its current spec. Until
// the repository controller lists b again, b's checks still pass for its
// parent's old head, so b would otherwise join the queue again.
func landed(b *gitk8s.GitBranch) bool {
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	return c != nil && c.Reason == reasonLanded && c.ObservedGeneration == b.Generation
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

// fixedOnly reports whether checks pushed every commit that b gained since
// its head was since, such as the base check's merge of the parent, so that
// b keeps its place in the queue.
func (m *merger) fixedOnly(ctx context.Context, b *gitk8s.GitBranch, since string) (bool, error) {
	local, remote, unlock, err := m.open(ctx, b)
	if err != nil {
		return false, err
	}
	defer unlock()
	if err := local.Fetch(ctx, remote, b.Spec.Branch); err != nil {
		return false, err
	}
	if ok, err := local.HasCommit(ctx, b.Spec.Head); err != nil || !ok {
		return false, errors.Join(err, fmt.Errorf("don't have %s after fetching; the branch moved, so waiting for the repository controller to list it again", gitk8s.Short(b.Spec.Head)))
	}
	// Fetching the head fetched every commit before it, so a missing earlier
	// head means that a push removed it.
	if ok, err := local.HasCommit(ctx, since); err != nil || !ok {
		return false, err
	}
	return local.OnlyFixerCommits(ctx, since, b.Spec.Head)
}

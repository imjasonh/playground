// Command check-base keeps branches up to date with their parents.
//
// When a branch doesn't contain its parent's head, the base check merges the
// parent in with a merge commit, and pushes the merge if the merge policy
// lets it. A merge that conflicts fails the check, with the conflicting
// paths in its message.
//
// A policy that lets the check push lands branches through the parent's merge
// queue, so the check merges the parent in only at the front of the queue.
// Until then, a branch that merges cleanly passes with outputs.behind set to
// "true".
package main

import (
	"cmp"
	"context"
	"fmt"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/signing"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"base,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// queued is a GitBranch's place in its parent's merge queue, which the merge
// controller writes.
type queued struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Status      struct {
		Queued *gitk8s.Queued `json:"queued,omitempty"`
	} `json:"status,omitzero"`
}

// first reports whether the branch is at the front of its parent's merge
// queue at head.
func first(ctx context.Context, meta *kube.ObjectMeta, head string) bool {
	b := kube.Get[queued](ctx, meta.Namespace, meta.Name)
	return b != nil && b.Status.Queued != nil && b.Status.Queued.Position == 1 && b.Status.Queued.Head == head
}

// stale runs the check again when a branch that it passed as behind its
// parent reaches the front of the queue.
func stale(ctx context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool {
	return previous.Outputs["behind"] == "true" && first(ctx, meta, spec.Head)
}

var check = checks.Check{Name: "base", UsesParent: true, FilesOnly: true, Stale: stale, Remote: credentials.Remote, SigningKey: signing.Key, Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	head, parentHead := in.Spec.Head, in.Spec.ParentHead
	ok, err := repo.IsAncestor(ctx, parentHead, head)
	if err != nil {
		return checks.Verdict{}, err
	}
	if ok {
		return checks.Pass("contains %s at %s", in.Spec.Parent, gitk8s.Short(parentHead)), nil
	}
	// Merging the parent into a branch that it already contains would make
	// a merge commit with no changes, which would then land on the parent.
	if merged, err := repo.IsAncestor(ctx, head, parentHead); err != nil || merged {
		return checks.Pass("%s already contains %s", in.Spec.Parent, gitk8s.Short(head)), err
	}
	tree, conflicts, err := repo.MergeTree(ctx, head, parentHead)
	if err != nil {
		return checks.Verdict{}, err
	}
	if len(conflicts) > 0 {
		v := checks.Fail("merging %s conflicts in %s", in.Spec.Parent, strings.Join(conflicts, ", "))
		v.Outputs = map[string]string{"conflicts": strings.Join(conflicts, ",")}
		return v, nil
	}
	if in.Policy.MayPush {
		if !first(ctx, in.Meta, head) {
			v := checks.Pass("behind %s at %s with no conflicts; waits for the front of %s's queue to merge it in",
				in.Spec.Parent, gitk8s.Short(parentHead), in.Spec.Parent)
			v.Outputs = map[string]string{"behind": "true"}
			return v, nil
		}
		// A merge of a parent that moved after it was listed would be behind
		// as soon as it was pushed, and the branch would merge again.
		if tip, err := repo.Fetched(ctx, in.Spec.Parent); err != nil || tip != parentHead {
			return checks.Verdict{}, cmp.Or(err, fmt.Errorf("%s moved to %s after it was listed at %s; waiting for the repository controller to list it again",
				in.Spec.Parent, gitk8s.Short(tip), gitk8s.Short(parentHead)))
		}
	}
	hc, err := repo.Commit(ctx, head)
	if err != nil {
		return checks.Verdict{}, err
	}
	pc, err := repo.Commit(ctx, parentHead)
	if err != nil {
		return checks.Verdict{}, err
	}
	msg := fmt.Sprintf("Merge %s into %s\n\n%s: base\n", in.Spec.Parent, in.Spec.Branch, git.FixerTrailer)
	fix, err := in.CommitTree(ctx, tree, []string{head, parentHead}, msg, max(hc.Time, pc.Time))
	if err != nil {
		return checks.Verdict{}, err
	}
	v := checks.Fail("%s is behind %s at %s", in.Spec.Branch, in.Spec.Parent, gitk8s.Short(parentHead))
	v.Fix = fix
	return v, nil
}

func main() { checks.Main[Branch](check) }

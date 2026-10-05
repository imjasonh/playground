// Command check-base keeps branches up to date with their parents.
//
// When a branch doesn't contain its parent's head, the base check merges the
// parent in with a merge commit, and pushes the merge if the merge policy
// lets it. A merge that conflicts fails the check, with the conflicting
// paths in its message.
package main

import (
	"context"
	"fmt"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/mirror"
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

var check = checks.Check{Name: "base", UsesParent: true, FilesOnly: true, Remote: mirror.Remote, Run: run}

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
	hc, err := repo.Commit(ctx, head)
	if err != nil {
		return checks.Verdict{}, err
	}
	pc, err := repo.Commit(ctx, parentHead)
	if err != nil {
		return checks.Verdict{}, err
	}
	msg := fmt.Sprintf("Merge %s into %s\n\n%s: base\n", in.Spec.Parent, in.Spec.Branch, git.FixerTrailer)
	fix, err := repo.CommitTree(ctx, tree, []string{head, parentHead}, msg, in.Identity, max(hc.Time, pc.Time))
	if err != nil {
		return checks.Verdict{}, err
	}
	v := checks.Fail("%s is behind %s at %s", in.Spec.Branch, in.Spec.Parent, gitk8s.Short(parentHead))
	v.Fix = fix
	return v, nil
}

func main() { checks.Main[Branch](check) }

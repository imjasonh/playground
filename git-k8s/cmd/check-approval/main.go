// Command check-approval passes branches that a person approved.
//
// To approve a branch, annotate its Branch object with the commit to approve
// and your username:
//
//	kubectl annotate --overwrite branches.git-k8s.imjasonh.com NAME \
//	  git-k8s.imjasonh.com/approve=SHA \
//	  git-k8s.imjasonh.com/approved-by="$(kubectl auth whoami -o jsonpath='{.status.userInfo.username}')"
//
// An approval is for a change: what the approved commit changes on top of
// its merge base with the parent's head. The approval check passes while the
// branch's head is the approved commit, or makes the same change on top of
// its own merge base with the parent's head, as git.Repo.SameChange compares
// them. So an approval holds when the base check merges the parent into the
// branch, and after a rebase or a squash that doesn't resolve a conflict. A
// push that adds, removes, or changes code needs a new approval. The
// approval must name the commit's full SHA, because anyone who can push can
// make a commit whose SHA starts with a short prefix. The check fails a
// shorter prefix, and the git-k8s-approvals admission policy rejects one.
//
// When the head isn't the approved commit, the check reads the repository
// through the mirror, and its passing result names the head's merge base
// with the parent's head. The merge controller lands the branch only when
// that merge base is the parent's head, so the files that land are the
// parent's head's files with the approved change applied.
//
// A passing result's approver output is the approved-by annotation, or
// empty without one, for merge gates that care who approved. The
// git-k8s-approvals admission policy in config/policy.yaml decides who can
// approve and checks approved-by.
package main

import (
	"context"
	"errors"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a Branch object.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=Branch,plural=branches,scope=Namespaced"`
	Spec        gitk8s.BranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"approval,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.BranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// The check reads an annotation, so it runs on every reconcile, including
// the one that a new annotation causes. An approval is for the change,
// which a squashed or rebased commit makes too, so it's FilesOnly. The
// check compares the approved commit's change with the head's in Run,
// instead of with SameChange, because a person can approve a commit after
// the head moves on from it, such as to base's merge of the parent.
var check = checks.Check{Name: "approval", Always: true, FilesOnly: true, Remote: mirror.Remote, Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	head := in.Spec.Head
	approved := in.Meta.Annotations[gitk8s.ApproveAnnotation]
	approver := in.Meta.Annotations[gitk8s.ApprovedByAnnotation]
	switch {
	case approved == "":
		return checks.Fail("%s isn't approved", gitk8s.Short(head)), nil
	case !git.IsObjectName(approved):
		return checks.Fail("the approval is for %s, which isn't a commit's full SHA", approved), nil
	case approved == head:
		if approver == "" {
			return pass(approver, "%s is approved", gitk8s.Short(head)), nil
		}
		return pass(approver, "%s is approved by %s", gitk8s.Short(head), approver), nil
	}
	ours, err := in.ChangeOf(ctx, approved)
	if errors.Is(err, checks.ErrUnknownCommit) {
		return checks.Fail("the approval is for %s, which isn't in the repository", gitk8s.Short(approved)), nil
	}
	if err != nil {
		return checks.Verdict{}, err
	}
	change, err := in.Change(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	same, err := in.SameChange(ctx, ours, change)
	switch {
	case err != nil:
		return checks.Verdict{}, err
	case !same:
		return checks.Fail("the approval is for %s, but the branch is at %s, which doesn't make the same change", gitk8s.Short(approved), gitk8s.Short(head)), nil
	}
	v := pass(approver, "%s is approved, and %s makes the same change", gitk8s.Short(approved), gitk8s.Short(head))
	if approver != "" {
		v = pass(approver, "%s is approved by %s, and %s makes the same change", gitk8s.Short(approved), approver, gitk8s.Short(head))
	}
	v.MergeBase = change.Base
	return v, nil
}

// pass returns a passing verdict with the approver output. The output is
// there even without approved-by, so a gate that compares the approver
// evaluates to false instead of failing.
func pass(approver, format string, args ...any) checks.Verdict {
	v := checks.Pass(format, args...)
	v.Outputs = map[string]string{"approver": approver}
	return v
}

func main() { checks.Main[Branch](check) }

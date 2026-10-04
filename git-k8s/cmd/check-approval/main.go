// Command check-approval passes branches that a person approved.
//
// To approve a branch, annotate its GitBranch with the commit to approve
// and your username:
//
//	kubectl annotate gitbranch NAME git-k8s.imjasonh.com/approve=SHA \
//	  git-k8s.imjasonh.com/approved-by="$(kubectl auth whoami -o jsonpath='{.status.userInfo.username}')"
//
// The approval check passes while the branch's head is that commit, so a
// later push needs a new approval. A passing result's approver output is
// the approved-by annotation, or empty without one, for merge gates that
// care who approved. The git-k8s-approvals admission policy in
// config/policy.yaml decides who can approve and checks approved-by.
package main

import (
	"context"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"approval,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// The check reads only the GitBranch, so it runs on every reconcile,
// including the one that a new annotation causes.
var check = checks.Check{Name: "approval", Always: true, Run: run}

func run(_ context.Context, in *checks.Input) (checks.Verdict, error) {
	head := in.Spec.Head
	approved := in.Meta.Annotations[gitk8s.ApproveAnnotation]
	switch {
	case len(approved) >= 7 && strings.HasPrefix(head, approved):
		approver := in.Meta.Annotations[gitk8s.ApprovedByAnnotation]
		v := checks.Pass("%s is approved", gitk8s.Short(head))
		if approver != "" {
			v = checks.Pass("%s is approved by %s", gitk8s.Short(head), approver)
		}
		// The key is there even without approved-by, so a gate that compares
		// the approver evaluates to false instead of failing.
		v.Outputs = map[string]string{"approver": approver}
		return v, nil
	case approved != "":
		return checks.Fail("the approval is for %s, but the branch is at %s", approved, gitk8s.Short(head)), nil
	}
	return checks.Fail("%s isn't approved", gitk8s.Short(head)), nil
}

func main() { checks.Main[Branch](check) }

package main

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/gate"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

// repositories reconciles GitRepository objects. A remote can't be
// watched, so each reconcile lists its branches and asks to run again after
// the repository's poll interval. A change to an owned GitBranch, such as a
// check result, also runs it, so the controller notices a fixer's push soon
// after the fixer reports it.
type repositories struct {
	git *git.Git
}

func (r *repositories) Reconcile(ctx context.Context, repo *gitk8s.GitRepository) error {
	ready := kube.Condition{Type: "Ready", Status: kube.False}
	defer func() { kube.SetCondition(&repo.Status.Conditions, ready) }()

	interval, err := time.ParseDuration(cmp.Or(repo.Spec.PollInterval, "30s"))
	if err != nil || interval < time.Second {
		ready.Reason = "InvalidPollInterval"
		ready.Message = fmt.Sprintf("pollInterval %q must be a duration of at least 1s", repo.Spec.PollInterval)
		return kube.Permanent(errors.New(ready.Message))
	}
	for _, rule := range repo.Spec.Branches {
		if rule.Merge == nil || rule.Merge.When == "" {
			continue
		}
		if _, err := gate.Parse(rule.Merge.When); err != nil {
			ready.Reason = "InvalidMergePolicy"
			ready.Message = fmt.Sprintf("branches rule %q: when: %v", rule.Match, err)
			return kube.Permanent(errors.New(ready.Message))
		}
	}

	remote, err := credentials.Remote(ctx, &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec})
	if err != nil {
		ready.Reason, ready.Message = "CredentialsUnavailable", err.Error()
		return err
	}
	// If listing fails, the error skips the declarations below, so the
	// framework keeps every GitBranch instead of pruning them.
	heads, err := r.git.LsRemote(ctx, remote)
	if err != nil {
		ready.Reason, ready.Message = "ListFailed", err.Error()
		return err
	}
	specs := gitk8s.DesiredBranches(repo.Name, repo.Spec.Branches, heads)
	for _, spec := range specs {
		kube.Own(ctx, &gitk8s.GitBranch{
			Object: kube.Meta(gitk8s.BranchObjectName(repo.Name, spec.Branch), map[string]string{gitk8s.RepositoryLabel: repo.Name}),
			Spec:   spec,
		})
	}
	repo.Status.Branches = int32(len(specs))
	ready = kube.Condition{
		Type:    "Ready",
		Status:  kube.True,
		Reason:  "Listed",
		Message: fmt.Sprintf("tracking %d of %d branches", len(specs), len(heads)),
	}
	kube.RequeueAfter(ctx, interval)
	return nil
}

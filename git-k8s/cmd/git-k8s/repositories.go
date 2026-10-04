package main

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"sync"
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
	// now is time.Now, except in tests.
	now func() time.Time
	// installPolicies is the -install-policies flag.
	installPolicies bool

	mu     sync.Mutex
	listed map[string]listing
}

// listing is what one git ls-remote of a repository found.
type listing struct {
	url   string
	at    time.Time
	heads map[string]string
}

// minListInterval is the shortest time between two listings of a
// repository. A branch's checks can report several results within a
// second, and each runs the reconcile again.
const minListInterval = 5 * time.Second

// recent returns the heads that a listing of url found less than window
// ago, and how long until the listing is that old.
func (r *repositories) recent(key, url string, window time.Duration) (map[string]string, time.Duration, bool) {
	r.mu.Lock()
	defer r.mu.Unlock()
	l, ok := r.listed[key]
	if age := r.clock().Sub(l.at); ok && l.url == url && age < window {
		return l.heads, window - age, true
	}
	return nil, 0, false
}

func (r *repositories) clock() time.Time {
	if r.now != nil {
		return r.now()
	}
	return time.Now()
}

func (r *repositories) remember(key, url string, heads map[string]string) {
	r.mu.Lock()
	defer r.mu.Unlock()
	now := r.clock()
	for k, l := range r.listed {
		if now.Sub(l.at) >= minListInterval {
			delete(r.listed, k)
		}
	}
	if r.listed == nil {
		r.listed = map[string]listing{}
	}
	r.listed[key] = listing{url: url, at: now, heads: heads}
}

func (r *repositories) Reconcile(ctx context.Context, repo *gitk8s.GitRepository) error {
	ready := kube.Condition{Type: "Ready", Status: kube.False}
	defer func() { kube.SetCondition(&repo.Status.Conditions, ready) }()
	kube.SetCondition(&repo.Status.Conditions, policiesCondition(ctx, r.installPolicies))

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

	key := repo.Namespace + "/" + repo.Name
	heads, wait, ok := r.recent(key, repo.Spec.URL, min(interval, minListInterval))
	if ok {
		// Declaring the same branches keeps them, and the reconcile lists
		// the remote once the last listing is old enough.
		kube.RequeueAfter(ctx, wait)
	} else {
		remote, err := credentials.Remote(ctx, &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec})
		if err != nil {
			ready.Reason, ready.Message = "CredentialsUnavailable", err.Error()
			return err
		}
		// If listing fails, the error skips the declarations below, so the
		// framework keeps every GitBranch instead of pruning them.
		if heads, err = r.git.LsRemote(ctx, remote); err != nil {
			ready.Reason, ready.Message = "ListFailed", err.Error()
			return err
		}
		r.remember(key, repo.Spec.URL, heads)
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

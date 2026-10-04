package main

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/gate"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// repositories reconciles GitRepository objects. Each reconcile syncs the
// repository's copy in the mirror with the external repository, and owns a
// GitBranch for each of the copy's branches that the rules select.
//
// The mirror triggers a reconcile after each push to it, and the merge
// controller after each landing, so a reconcile reads the copy, which is
// cheap, and pushes what changed. The external repository can't be watched,
// so a reconcile fetches from it only once each poll interval.
type repositories struct {
	mirror *mirror.Mirror
	// now is time.Now, except in tests.
	now func() time.Time

	mu    sync.Mutex
	polls map[string]poll
}

// poll is when a repository's reconcile next contacts its external
// repository.
type poll struct {
	url string
	// next is when to fetch from the external repository again.
	next time.Time
	// failure is why the last fetch or push failed, or "" if it didn't.
	// Until next, reconciles don't push either.
	failure string
}

// retryInterval is the longest wait before a reconcile tries again to
// reach an external repository that failed.
const retryInterval = 30 * time.Second

// finalizer is the finalizer that kube adds to each GitRepository for the
// repositories controller.
const finalizer = "kube.imjasonh.github.io/repositories"

func (r *repositories) clock() time.Time {
	if r.now != nil {
		return r.now()
	}
	return time.Now()
}

func (r *repositories) poll(key, url string) poll {
	r.mu.Lock()
	defer r.mu.Unlock()
	if p := r.polls[key]; p.url == url {
		return p
	}
	return poll{url: url}
}

// polled records what a sync that started at now did, and returns the
// repository's new poll.
func (r *repositories) polled(key string, p poll, now time.Time, interval time.Duration, rep *mirror.Report, pushed bool) poll {
	switch {
	case rep.Err != nil:
		p.failure = rep.Err.Error()
		p.next = now.Add(min(interval, retryInterval))
	case rep.Fetched || pushed:
		p.failure = ""
		if rep.Fetched {
			p.next = now.Add(interval)
		}
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.polls == nil {
		r.polls = map[string]poll{}
	}
	r.polls[key] = p
	return p
}

func (r *repositories) forget(key string) {
	r.mu.Lock()
	defer r.mu.Unlock()
	delete(r.polls, key)
}

func (r *repositories) Reconcile(ctx context.Context, repo *gitk8s.GitRepository) error {
	ready := kube.Condition{Type: "Ready", Status: kube.False}
	defer func() { kube.SetCondition(&repo.Status.Conditions, ready) }()
	kube.SetCondition(&repo.Status.Conditions, policiesCondition(ctx))

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
	now := r.clock()
	p := r.poll(key, repo.Spec.URL)
	fetch := !now.Before(p.next)
	push := fetch || p.failure == ""
	spec := &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec}
	var credErr error
	rep, err := r.mirror.Sync(ctx, spec, mirror.SyncOptions{
		Fetch: fetch,
		Push:  push,
		Remote: func() (git.Remote, error) {
			remote, err := credentials.Remote(ctx, spec)
			credErr = err
			return remote, err
		},
	})
	if err != nil {
		// Without a report, the error skips the declarations below, so the
		// framework keeps every GitBranch instead of pruning them.
		switch {
		case credErr != nil:
			ready.Reason = "CredentialsUnavailable"
		case errors.Is(err, mirror.ErrNotSynced):
			ready.Reason = "FetchFailed"
		default:
			ready.Reason = "MirrorFailed"
		}
		ready.Message = err.Error()
		return err
	}
	p = r.polled(key, p, now, interval, rep, push)

	specs := gitk8s.DesiredBranches(repo.Name, repo.Spec.Branches, rep.Heads)
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
		Message: fmt.Sprintf("tracking %d of %d branches", len(specs), len(rep.Heads)),
	}
	kube.SetCondition(&repo.Status.Conditions, syncedCondition(p, rep))
	noticeDivergence(ctx, repo, rep.Diverged)
	kube.RequeueAfter(ctx, p.next.Sub(now))
	return nil
}

// syncedCondition reports whether the external repository has every change
// in the mirror's copy.
func syncedCondition(p poll, rep *mirror.Report) kube.Condition {
	c := kube.Condition{Type: "ExternalSynced", Status: kube.False}
	switch {
	case p.failure != "":
		c.Reason, c.Message = "SyncFailed", p.failure
	case len(rep.Diverged) > 0:
		c.Reason = "Diverged"
		c.Message = strings.Join(slices.Sorted(maps.Keys(rep.Diverged)), ", ") +
			" changed both in the mirror and in the external repository; the mirror keeps the external repository's heads under refs/git-k8s/downstream/heads/"
	case len(rep.Pending) > 0:
		c.Reason = "Pending"
		c.Message = "the external repository doesn't have the mirror's changes to " + strings.Join(rep.Pending, ", ") + " yet"
	default:
		c.Status, c.Reason, c.Message = kube.True, "InSync", "the external repository has every change in the mirror"
	}
	if len(c.Message) > 1024 {
		c.Message = c.Message[:1021] + "..."
	}
	return c
}

// noticeDivergence triggers a reconcile of each of repo's GitBranches whose
// status.diverged doesn't match diverged, so the merge controller updates
// it. A divergence doesn't move the branch's head in the mirror, so nothing
// else changes the GitBranch.
func noticeDivergence(ctx context.Context, repo *gitk8s.GitRepository, diverged map[string]string) {
	branches := kube.List[gitk8s.GitBranch](ctx, kube.InNamespace(repo.Namespace),
		kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: repo.Name}))
	for _, b := range branches {
		want, have := diverged[b.Spec.Branch], b.Status.Diverged
		if (have == nil) != (want == "") || (have != nil && have.Commit != want) {
			kube.Trigger[gitk8s.GitBranch](ctx, b.Namespace, b.Name)
		}
	}
}

// Finalize pushes the last changes in the mirror's copy of repo to the
// external repository, and then deletes the copy. While the external
// repository lacks a change that the mirror accepted, Finalize fails, and
// the GitRepository stays.
func (r *repositories) Finalize(ctx context.Context, repo *gitk8s.GitRepository) error {
	spec := &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec}
	rep, err := r.mirror.Sync(ctx, spec, mirror.SyncOptions{
		Push:   true,
		Final:  true,
		Remote: func() (git.Remote, error) { return credentials.Remote(ctx, spec) },
	})
	if err != nil {
		return err
	}
	var unsynced []string
	if len(rep.Pending) > 0 {
		unsynced = append(unsynced, "doesn't have the mirror's changes to "+strings.Join(rep.Pending, ", "))
	}
	if len(rep.Diverged) > 0 {
		unsynced = append(unsynced, "diverged from the mirror on "+strings.Join(slices.Sorted(maps.Keys(rep.Diverged)), ", "))
	}
	if rep.Err != nil {
		unsynced = append(unsynced, rep.Err.Error())
	}
	if len(unsynced) > 0 {
		return fmt.Errorf("the mirror keeps its copy until the external repository has every change in it, but the external repository %s; to delete the copy and the changes, remove the finalizer %s",
			strings.Join(unsynced, "; "), finalizer)
	}
	r.forget(repo.Namespace + "/" + repo.Name)
	return r.mirror.Delete(ctx, spec)
}

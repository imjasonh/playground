package main

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/gate"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// merger reconciles Branch objects. It's the only controller that
// reconciles the full Branch type, so its manager installs the
// CustomResourceDefinition.
type merger struct {
	mirror *mirror.Mirror
	ident  git.Identity
}

func (m *merger) Reconcile(ctx context.Context, b *gitk8s.Branch) error {
	results := b.Status.Checks
	// The results controller manages status.checks. Leaving it out of this
	// controller's status write keeps server-side apply from making this
	// controller a manager of the check results.
	b.Status.Checks = nil
	q, err := queue(ctx, b)
	b.Status.Queue = q
	if err != nil {
		return err
	}

	repo := kube.Get[gitk8s.RepositoryView](ctx, b.Namespace, b.Spec.Repository)
	diverged, err := m.diverged(ctx, repo, b.Spec.Branch)
	if err != nil {
		// kube writes the status of a failed reconcile too, so b keeps its
		// place in the queue.
		return err
	}
	b.Status.Diverged = diverged
	queued := b.Status.Queued
	b.Status.Queued = nil

	spec := &b.Spec
	switch {
	case landed(b):
		return nil
	case spec.Parent == "":
		b.Status.State = ""
		b.Status.Conditions = slices.DeleteFunc(b.Status.Conditions, func(c kube.Condition) bool { return c.Type == "Landed" })
		return nil
	case diverged != nil:
		// Landing the mirror's head would leave out the external
		// repository's changes. Branches still land on a diverged parent,
		// since the commit that resolves the parent can land on it from a
		// child branch.
		external := "has it at " + gitk8s.Short(diverged.Commit)
		if diverged.Commit == "" {
			external = "deleted it"
		}
		report(b, gitk8s.MergeStateDiverged, "%s changed both in the mirror and in the external repository, which %s; waiting for a commit that keeps both sides' changes",
			spec.Branch, external)
		return nil
	case spec.Merge == nil:
		report(b, gitk8s.MergeStateNoMergePolicy, "no branches rule that matches %s has a merge policy", spec.Parent)
		return nil
	case spec.ParentHead == "":
		report(b, gitk8s.MergeStateParentMissing, "%s doesn't exist in the mirror", spec.Parent)
		return nil
	case spec.Head == spec.ParentHead:
		// A branch at its parent's head can be new, such as one just created
		// from the parent, so it's Landed only if this controller landed it
		// and it stayed.
		if c := kube.FindCondition(b.Status.Conditions, "Landed"); c != nil && c.Status == kube.True {
			report(b, gitk8s.MergeStateLanded, "%s", c.Message)
			return nil
		}
		report(b, gitk8s.MergeStateNothingToLand, "%s is at %s", spec.Parent, gitk8s.Short(spec.Head))
		return nil
	}

	checks := gitk8s.GateChecks(spec.Merge, results, spec.Head, spec.ParentHead)
	pass, err := evaluate(spec.Merge, checks)
	switch {
	case err != nil && !anyPending(checks):
		report(b, gitk8s.MergeStateInvalidGate, "when: %v", err)
		return nil
	case queues(spec.Merge):
		return m.queued(ctx, repo, b, queued, checks, results, err == nil && pass)
	case err != nil || !pass:
		report(b, gitk8s.MergeStateWaitingForChecks, "%s", describe(spec.Merge, checks))
		return nil
	}
	return m.land(ctx, repo, b, results)
}

// diverged returns how branch diverged between the mirror's copy of repo
// and the external repository, or nil if it didn't, or there's no copy.
func (m *merger) diverged(ctx context.Context, repo *gitk8s.RepositoryView, branch string) (*gitk8s.Divergence, error) {
	if repo == nil {
		return nil, nil
	}
	d, err := m.mirror.Divergence(ctx, repo, branch)
	if errors.Is(err, mirror.ErrNotSynced) {
		return nil, nil
	}
	return d, err
}

// evaluate reports whether a merge policy's gate passes.
func evaluate(policy *gitk8s.MergePolicy, checks map[string]gitk8s.GateCheck) (bool, error) {
	if policy.When == "" {
		for _, c := range checks {
			if !c.Passed {
				return false, nil
			}
		}
		return true, nil
	}
	g, err := gate.Parse(policy.When, policy.Checks)
	if err != nil {
		return false, err
	}
	return g.Eval(checks)
}

func anyPending(checks map[string]gitk8s.GateCheck) bool {
	for _, c := range checks {
		if c.State == gitk8s.Pending || c.State == gitk8s.Running {
			return true
		}
	}
	return false
}

// describe lists the checks' states, for the message of a branch whose gate
// doesn't pass yet.
func describe(policy *gitk8s.MergePolicy, checks map[string]gitk8s.GateCheck) string {
	var parts []string
	for _, c := range policy.Checks {
		gc := checks[c.Name]
		s := c.Name + " " + gc.State
		if level := gc.Outputs["level"]; level != "" {
			s += " (" + level + ")"
		}
		parts = append(parts, s)
	}
	slices.Sort(parts)
	msg := "checks: " + strings.Join(parts, ", ")
	if policy.When != "" {
		msg += "; when: " + policy.When
	}
	return msg
}

// land fast-forwards the parent to the branch's head in the mirror's copy
// of repo, or squashes or rebases the branch onto it when the merge policy
// says to. The repository controller then pushes the parent to the
// external repository.
func (m *merger) land(ctx context.Context, repo *gitk8s.RepositoryView, b *gitk8s.Branch, results map[string]gitk8s.CheckResult) error {
	spec := &b.Spec
	if repo == nil {
		return fmt.Errorf("the Repository object %s/%s doesn't exist", b.Namespace, spec.Repository)
	}
	local, err := m.mirror.Open(ctx, repo)
	if err != nil {
		return err
	}
	defer local.Close()
	for _, sha := range []string{spec.Head, spec.ParentHead} {
		if ok, err := local.HasCommit(ctx, sha); err != nil || !ok {
			return errors.Join(err, fmt.Errorf("the mirror doesn't have %s; waiting for the repository controller to list the branches again", gitk8s.Short(sha)))
		}
	}
	contained, err := local.IsAncestor(ctx, spec.Head, spec.ParentHead)
	if err != nil {
		return err
	}
	if contained {
		report(b, gitk8s.MergeStateNothingToLand, "%s already contains %s", spec.Parent, gitk8s.Short(spec.Head))
		return nil
	}
	ff, err := local.IsAncestor(ctx, spec.ParentHead, spec.Head)
	if err != nil {
		return err
	}
	if !ff {
		report(b, gitk8s.MergeStateNotFastForward, "%s doesn't contain %s at %s, so it can't land on %s",
			spec.Branch, spec.Parent, gitk8s.Short(spec.ParentHead), spec.Parent)
		return nil
	}
	// A result for the head's change on top of an older merge base waits for
	// its check to see the change on top of the parent's head, which is what
	// lands.
	checks := gitk8s.LandingGateChecks(spec.Merge, results, spec.Head, spec.ParentHead)
	if pass, err := evaluate(spec.Merge, checks); err != nil || !pass {
		report(b, gitk8s.MergeStateWaitingForChecks, "%s", describe(spec.Merge, checks))
		return nil
	}
	switch spec.Merge.Landing {
	case gitk8s.Squash, gitk8s.Rebase:
		if done, err := m.rewrite(ctx, repo, local.Repo, b, results); err != nil || done {
			return err
		}
	}
	deleted, err := fastForward(ctx, local, b)
	if err != nil {
		return fmt.Errorf("fast-forwarding %s to %s: %w", spec.Parent, gitk8s.Short(spec.Head), err)
	}
	slog.Info("landed", "namespace", b.Namespace, "repository", spec.Repository, "branch", spec.Branch,
		"parent", spec.Parent, "from", gitk8s.Short(spec.ParentHead), "to", gitk8s.Short(spec.Head), "deletedBranch", deleted)
	report(b, gitk8s.MergeStateLanded, "fast-forwarded %s from %s to %s", spec.Parent, gitk8s.Short(spec.ParentHead), gitk8s.Short(spec.Head))
	kube.Eventf(ctx, kube.Normal, "Landed", "fast-forwarded %s from %s to %s at %s", spec.Parent, gitk8s.Short(spec.ParentHead), spec.Branch, gitk8s.Short(spec.Head))
	if deleted {
		kube.Eventf(ctx, kube.Normal, "DeletedBranch", "deleted %s at %s after it landed on %s", spec.Branch, gitk8s.Short(spec.Head), spec.Parent)
	}
	kube.Trigger[gitk8s.Repository](ctx, b.Namespace, spec.Repository)
	return nil
}

// fastForward moves the parent to the branch's head in the mirror's copy,
// and reports whether it deleted the branch. When the merge policy deletes
// landed branches, the deletion goes in the same update, with a lease on
// the branch's head, so a landed branch can't stay because the controller
// stopped or failed between two updates. If the branch moved or was deleted
// since the repository controller listed it, the parent still moves to the
// listed head, and the branch stays as it is. The repository controller
// pushes the deletion to the external repository, and the Repository object's
// ExternalSynced condition reports the external repository's reason if it
// refuses, as for a protected branch.
func fastForward(ctx context.Context, local *mirror.Repository, b *gitk8s.Branch) (bool, error) {
	spec := &b.Spec
	parent := git.RefUpdate{Ref: "refs/heads/" + spec.Parent, New: spec.Head, Old: spec.ParentHead}
	if !spec.Merge.DeleteLandedBranches {
		return false, local.UpdateRefs(ctx, parent)
	}
	rejected := local.UpdateRefs(ctx, parent, git.RefUpdate{Ref: "refs/heads/" + spec.Branch, Old: spec.Head})
	if !errors.Is(rejected, git.ErrRejected) {
		return rejected == nil, rejected
	}
	// Either lease failed. If it was the parent's, this fails too.
	if err := local.UpdateRefs(ctx, parent); err != nil {
		return false, err
	}
	slog.Info("not deleting a landed branch that moved or was deleted since the repository controller listed it",
		"namespace", b.Namespace, "branch", spec.Branch, "err", rejected)
	return false, nil
}

// report sets the Landed condition, which is True only in
// MergeStateLanded, and State to the condition's reason.
func report(b *gitk8s.Branch, state gitk8s.MergeState, format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	if len(msg) > 1024 {
		msg = msg[:1021] + "..."
	}
	c := kube.Condition{Type: "Landed", Status: kube.False, Reason: string(state), Message: msg, ObservedGeneration: b.Generation}
	if state == gitk8s.MergeStateLanded {
		c.Status = kube.True
	}
	kube.SetCondition(&b.Status.Conditions, c)
	b.Status.State = state
}

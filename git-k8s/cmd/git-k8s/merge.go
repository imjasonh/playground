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

// merger reconciles GitBranch objects. It's the only controller that
// reconciles the full GitBranch type, so its manager installs the
// CustomResourceDefinition.
type merger struct {
	mirror *mirror.Mirror
	ident  git.Identity
}

// Merged condition reasons, which State repeats.
const (
	reasonNoMergePolicy    = "NoMergePolicy"
	reasonParentMissing    = "ParentMissing"
	reasonDiverged         = "Diverged"
	reasonWaitingForChecks = "WaitingForChecks"
	reasonInvalidGate      = "InvalidGate"
	reasonNotFastForward   = "NotFastForward"
	reasonLanded           = "Landed"
	reasonMerged           = "Merged"
	reasonQueued           = "Queued"
)

func (m *merger) Reconcile(ctx context.Context, b *gitk8s.GitBranch) error {
	results := b.Status.Checks
	// Check controllers manage status.checks. Leaving it out of this
	// controller's status write keeps server-side apply from making this
	// controller a manager of their entries.
	b.Status.Checks = nil
	q, err := queue(ctx, b)
	b.Status.Queue = q
	if err != nil {
		return err
	}
	queued := b.Status.Queued
	b.Status.Queued = nil

	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	diverged, err := m.diverged(ctx, repo, b.Spec.Branch)
	if err != nil {
		return err
	}
	b.Status.Diverged = diverged

	spec := &b.Spec
	switch {
	case landed(b):
		return nil
	case spec.Parent == "":
		b.Status.State = ""
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
		report(b, reasonDiverged, false, "%s changed both in the mirror and in the external repository, which %s; waiting for a commit that keeps both sides' changes",
			spec.Branch, external)
		return nil
	case spec.Merge == nil:
		report(b, reasonNoMergePolicy, false, "no branches rule that matches %s has a merge policy", spec.Parent)
		return nil
	case spec.ParentHead == "":
		report(b, reasonParentMissing, false, "%s doesn't exist in the mirror", spec.Parent)
		return nil
	case spec.Head == spec.ParentHead:
		// A branch that's already merged can be new, such as one just
		// created from the parent, so only a branch that this controller
		// lands is deleted.
		report(b, reasonMerged, true, "%s is at %s", spec.Parent, gitk8s.Short(spec.Head))
		return nil
	}

	checks := gitk8s.GateChecks(spec.Merge, results, spec.Head, spec.ParentHead)
	pass, err := evaluate(spec.Merge, checks)
	switch {
	case err != nil && !anyPending(checks):
		report(b, reasonInvalidGate, false, "when: %v", err)
		return nil
	case queues(spec.Merge):
		return m.queued(ctx, repo, b, queued, checks, results, err == nil && pass)
	case err != nil || !pass:
		report(b, reasonWaitingForChecks, false, "%s", describe(spec.Merge, checks))
		return nil
	}
	return m.land(ctx, repo, b, results)
}

// diverged returns how branch diverged between the mirror's copy of repo
// and the external repository, or nil if it didn't, or there's no copy.
func (m *merger) diverged(ctx context.Context, repo *gitk8s.Repository, branch string) (*gitk8s.Divergence, error) {
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
	g, err := gate.Parse(policy.When)
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
func (m *merger) land(ctx context.Context, repo *gitk8s.Repository, b *gitk8s.GitBranch, results map[string]gitk8s.CheckResult) error {
	spec := &b.Spec
	if repo == nil {
		return fmt.Errorf("GitRepository %s/%s doesn't exist", b.Namespace, spec.Repository)
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
		report(b, reasonMerged, true, "%s already contains %s", spec.Parent, gitk8s.Short(spec.Head))
		return nil
	}
	ff, err := local.IsAncestor(ctx, spec.ParentHead, spec.Head)
	if err != nil {
		return err
	}
	if !ff {
		report(b, reasonNotFastForward, false, "%s doesn't contain %s at %s, so it can't land on %s",
			spec.Branch, spec.Parent, gitk8s.Short(spec.ParentHead), spec.Parent)
		return nil
	}
	switch spec.Merge.Landing {
	case gitk8s.Squash, gitk8s.Rebase:
		if done, err := m.rewrite(ctx, repo, local.Repo, b, results); err != nil || done {
			return err
		}
	}
	err = local.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/" + spec.Parent, New: spec.Head, Old: spec.ParentHead})
	if err != nil {
		return fmt.Errorf("fast-forwarding %s to %s: %w", spec.Parent, gitk8s.Short(spec.Head), err)
	}
	slog.Info("landed", "namespace", b.Namespace, "repository", spec.Repository, "branch", spec.Branch,
		"parent", spec.Parent, "from", gitk8s.Short(spec.ParentHead), "to", gitk8s.Short(spec.Head))
	report(b, reasonLanded, true, "fast-forwarded %s from %s to %s", spec.Parent, gitk8s.Short(spec.ParentHead), gitk8s.Short(spec.Head))
	kube.Eventf(ctx, kube.Normal, reasonLanded, "fast-forwarded %s from %s to %s at %s", spec.Parent, gitk8s.Short(spec.ParentHead), spec.Branch, gitk8s.Short(spec.Head))
	err = deleteBranch(ctx, local, b)
	kube.Trigger[gitk8s.GitRepository](ctx, b.Namespace, spec.Repository)
	return err
}

// deleteBranch deletes a branch that just landed if the merge policy says
// to, with a lease so that a branch that moved since it landed stays.
func deleteBranch(ctx context.Context, local *mirror.Repository, b *gitk8s.GitBranch) error {
	if !b.Spec.Merge.DeleteMergedBranches {
		return nil
	}
	err := local.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/" + b.Spec.Branch, Old: b.Spec.Head})
	if errors.Is(err, git.ErrRejected) {
		slog.Info("not deleting a branch that moved after it merged", "namespace", b.Namespace, "branch", b.Spec.Branch)
		return nil
	}
	if err != nil {
		return fmt.Errorf("deleting merged branch %s: %w", b.Spec.Branch, err)
	}
	slog.Info("deleted merged branch", "namespace", b.Namespace, "repository", b.Spec.Repository, "branch", b.Spec.Branch)
	kube.Eventf(ctx, kube.Normal, "DeletedBranch", "deleted %s at %s after it landed on %s", b.Spec.Branch, gitk8s.Short(b.Spec.Head), b.Spec.Parent)
	return nil
}

// report sets the Merged condition, and State to the condition's reason.
func report(b *gitk8s.GitBranch, reason string, merged bool, format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	if len(msg) > 1024 {
		msg = msg[:1021] + "..."
	}
	c := kube.Condition{Type: "Merged", Status: kube.False, Reason: reason, Message: msg, ObservedGeneration: b.Generation}
	if merged {
		c.Status = kube.True
	}
	kube.SetCondition(&b.Status.Conditions, c)
	b.Status.State = reason
}

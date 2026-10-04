package main

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// More Merged condition reasons, for squash and rebase landings.
const (
	// reasonNeedsRebase means a squash or rebase landing can't copy the
	// branch's commits onto the parent's head, so a person has to rebase
	// them.
	reasonNeedsRebase = "NeedsRebase"
	// reasonRewritten means the merge controller pushed the squashed or
	// rebased commits to the branch instead of the parent, so that the
	// checks whose results don't have filesOnly run on them.
	reasonRewritten = "Rewritten"
)

// maxLandingCommits is the most commits that a squash or rebase landing
// reads from a branch. A rebase runs two git commands for each commit that
// it copies.
const maxLandingCommits = 1000

// rewrite lands a branch whose merge policy squashes or rebases it, and
// reports the outcome. It does nothing and returns false when the branch's
// head can land as it is, by fast-forward.
func (m *merger) rewrite(ctx context.Context, local *git.Repo, remote git.Remote, b *gitk8s.GitBranch, results map[string]gitk8s.CheckResult) (bool, error) {
	spec := &b.Spec
	if keep, err := keepsHead(ctx, local, spec); err != nil || keep {
		return false, err
	}
	verb := "squashed"
	if spec.Merge.Landing == gitk8s.Rebase {
		verb = "rebased"
	}
	landed, problem, err := m.squashOrRebase(ctx, local, spec)
	switch {
	case err != nil:
		return false, err
	case problem != "":
		report(b, reasonNeedsRebase, false, "can't %s %s onto %s at %s, because %s",
			strings.ToLower(spec.Merge.Landing), spec.Branch, spec.Parent, gitk8s.Short(spec.ParentHead), problem)
		return true, nil
	case landed == spec.Head:
		return false, nil
	case landed == spec.ParentHead:
		report(b, reasonMerged, true, "%s at %s already has the changes in %s", spec.Parent, gitk8s.Short(spec.ParentHead), gitk8s.Short(spec.Head))
		return true, nil
	}

	if pass, err := evaluate(spec.Merge, gitk8s.RewrittenGateChecks(spec.Merge, results, spec.Head, spec.ParentHead)); err != nil || !pass {
		var rerun []string
		for _, c := range spec.Merge.Checks {
			if r, ok := results[c.Name]; ok && !r.FilesOnly && r.Fresh(spec.Head, spec.ParentHead) {
				rerun = append(rerun, c.Name)
			}
		}
		if err := local.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + spec.Branch, New: landed, Old: spec.Head}); err != nil {
			return true, fmt.Errorf("pushing %s to %s: %w", gitk8s.Short(landed), spec.Branch, err)
		}
		slog.Info("rewrote a branch", "namespace", b.Namespace, "repository", spec.Repository, "branch", spec.Branch,
			"landing", spec.Merge.Landing, "from", gitk8s.Short(spec.Head), "to", gitk8s.Short(landed))
		report(b, reasonRewritten, false, "%s %s onto %s at %s as %s and pushed it to %s, because the results of %s might depend on the branch's commits",
			verb, spec.Branch, spec.Parent, gitk8s.Short(spec.ParentHead), gitk8s.Short(landed), spec.Branch, strings.Join(rerun, ", "))
		return true, nil
	}

	// The branch moves or goes in the same push, so a branch that isn't
	// deleted stays in its parent instead of falling behind it.
	branch := git.RefUpdate{Ref: "refs/heads/" + spec.Branch, New: landed, Old: spec.Head}
	if spec.Merge.DeleteMergedBranches {
		branch.New = ""
	}
	err = local.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + spec.Parent, New: landed, Old: spec.ParentHead}, branch)
	if err != nil {
		return true, fmt.Errorf("landing %s on %s: %w", gitk8s.Short(landed), spec.Parent, err)
	}
	slog.Info("landed", "namespace", b.Namespace, "repository", spec.Repository, "branch", spec.Branch, "parent", spec.Parent,
		"landing", spec.Merge.Landing, "from", gitk8s.Short(spec.ParentHead), "to", gitk8s.Short(landed), "deletedBranch", branch.New == "")
	report(b, reasonLanded, true, "%s %s onto %s, which moved from %s to %s", verb, spec.Branch, spec.Parent, gitk8s.Short(spec.ParentHead), gitk8s.Short(landed))
	return true, nil
}

// keepsHead reports whether the branch's head already is what a squash or
// rebase makes, without reading the branch's log. land calls rewrite only
// for a branch that contains the parent's head, so a branch without merges
// already builds on it, and a branch of one commit on top of it is already
// squashed.
func keepsHead(ctx context.Context, local *git.Repo, spec *gitk8s.GitBranchSpec) (bool, error) {
	if spec.Merge.Landing == gitk8s.Rebase {
		merges, err := local.HasMerge(ctx, spec.ParentHead, spec.Head)
		return !merges, err
	}
	parents, err := local.Parents(ctx, spec.Head)
	return slices.Equal(parents, []string{spec.ParentHead}), err
}

// squashOrRebase reads the branch's commits and squashes or rebases them
// onto the parent's head. A problem says why it can't.
func (m *merger) squashOrRebase(ctx context.Context, local *git.Repo, spec *gitk8s.GitBranchSpec) (landed, problem string, err error) {
	log, err := local.Log(ctx, spec.ParentHead, spec.Head, maxLandingCommits+1)
	switch {
	case errors.Is(err, git.ErrLogTooBig):
		return "", fmt.Sprintf("%s's commits have more than %d MiB of messages, names, and other text", spec.Branch, git.MaxLogBytes>>20), nil
	case err != nil:
		return "", "", err
	case len(log) > maxLandingCommits:
		return "", fmt.Sprintf("%s has more than %d commits that %s doesn't have", spec.Branch, maxLandingCommits, spec.Parent), nil
	case len(log) == 0 || log[len(log)-1].SHA != spec.Head:
		return "", "", fmt.Errorf("git log of %s doesn't end at its head %s", spec.Branch, gitk8s.Short(spec.Head))
	}
	parent, err := local.Commit(ctx, spec.ParentHead)
	if err != nil {
		return "", "", err
	}
	if spec.Merge.Landing == gitk8s.Squash {
		return m.squash(ctx, local, spec, log, parent)
	}
	return m.rebase(ctx, local, spec, log, parent)
}

// squash returns a commit with the branch head's files on top of the
// parent's head. It returns the head when the branch is this controller's
// commit on the parent's head followed only by checks' fixes, and the
// parent's head when the branch changes no files. A problem says why the
// branch can't be squashed.
func (m *merger) squash(ctx context.Context, local *git.Repo, spec *gitk8s.GitBranchSpec, log []git.LogEntry, parent git.Commit) (landed, problem string, err error) {
	head := log[len(log)-1]
	switch {
	case m.fixedAfterSquash(spec, log):
		return spec.Head, "", nil
	case head.Tree == parent.Tree:
		return spec.ParentHead, "", nil
	}
	from, message := squashMessage(log)
	if problem := copyProblem(from); problem != "" {
		return "", problem, nil
	}
	landed, err = local.WriteCommit(ctx, git.NewCommit{
		Tree:      head.Tree,
		Parents:   []string{spec.ParentHead},
		Author:    from.Author,
		Committer: m.committer(max(head.Time, parent.Time)),
		Message:   message,
	})
	return landed, "", err
}

// fixedAfterSquash reports whether log starts with a commit that this
// controller made on the parent's head, such as a squash that it pushed to
// the branch, and has only checks' fixes after it. Squashing such a branch
// again would leave out the fixes, so their count would start again, and a
// check whose fix the squash undoes would push it forever.
func (m *merger) fixedAfterSquash(spec *gitk8s.GitBranchSpec, log []git.LogEntry) bool {
	first := log[0]
	return slices.Equal(first.Parents, []string{spec.ParentHead}) && first.Committer == m.ident &&
		!slices.ContainsFunc(log[1:], func(c git.LogEntry) bool { return !c.Fixer() })
}

// squashMessage returns the commit whose author a commit that squashes
// log's commits takes, and the squashed commit's message. When one commit
// that isn't a merge or a check's fix makes the change, the squashed
// commit takes its author and message. Otherwise the message lists every
// commit's subject, keeps the trailers of the commits that aren't fixes,
// such as Signed-off-by, and credits the other authors with
// Co-authored-by trailers. The message never has the fixer trailer, so the
// squashed commit doesn't count as a fix.
func squashMessage(log []git.LogEntry) (from git.LogEntry, message string) {
	var commits, people []git.LogEntry
	for _, c := range log {
		if len(c.Parents) > 1 {
			continue
		}
		commits = append(commits, c)
		if !c.Fixer() {
			people = append(people, c)
		}
	}
	if len(commits) == 0 {
		commits = log[len(log)-1:]
	}
	if len(people) == 0 {
		people = commits
	}
	first := people[0]
	if len(people) == 1 {
		return first, withoutFixerTrailers(first.Message)
	}
	var msg strings.Builder
	msg.WriteString(first.Subject() + "\n\n")
	for _, c := range commits {
		msg.WriteString("* " + c.Subject() + "\n")
	}
	var trailers []string
	for _, c := range people {
		trailers = append(trailers, c.Trailers...)
	}
	credited := map[string]bool{strings.ToLower(first.Author.Email): true}
	for _, c := range people {
		if email := strings.ToLower(c.Author.Email); !credited[email] {
			credited[email] = true
			trailers = append(trailers, fmt.Sprintf("Co-authored-by: %s <%s>", c.Author.Name, c.Author.Email))
		}
	}
	seen := map[string]bool{}
	trailers = slices.DeleteFunc(trailers, func(t string) bool {
		dup := seen[t]
		seen[t] = true
		return dup
	})
	if len(trailers) > 0 {
		msg.WriteString("\n" + strings.Join(trailers, "\n") + "\n")
	}
	return first, withoutFixerTrailers(msg.String())
}

// withoutFixerTrailers returns msg without the lines that git's trailer
// parser reads as the fixer trailer. The parser ignores the key's case and
// spaces before the colon, and prints such a trailer as "Git-K8s-Fixer: x".
func withoutFixerTrailers(msg string) string {
	lines := strings.Split(msg, "\n")
	kept := slices.DeleteFunc(slices.Clone(lines), func(line string) bool {
		key, _, ok := strings.Cut(line, ":")
		return ok && strings.EqualFold(strings.TrimSpace(key), git.FixerTrailer)
	})
	if len(kept) == len(lines) {
		return msg
	}
	return strings.TrimRight(strings.Join(kept, "\n"), "\n") + "\n"
}

// rebase copies each of the branch's commits that isn't a merge onto the
// parent's head, in order, and returns the last copy. It keeps a commit
// whose parent is already the commit to copy onto, so a branch whose
// commits all build on the parent's head returns its head. It leaves out a
// commit that changes nothing on top of the earlier ones, and returns the
// parent's head when that leaves no commits. A problem says why the
// branch can't be rebased.
func (m *merger) rebase(ctx context.Context, local *git.Repo, spec *gitk8s.GitBranchSpec, log []git.LogEntry, parent git.Commit) (landed, problem string, err error) {
	onto, tree, when := spec.ParentHead, parent.Tree, parent.Time
	for _, c := range log {
		switch {
		case len(c.Parents) > 1:
			continue
		case len(c.Parents) == 0:
			return "", fmt.Sprintf("%s has no parent", gitk8s.Short(c.SHA)), nil
		case c.Parents[0] == onto:
			onto, tree, when = c.SHA, c.Tree, max(c.Time, when)
			continue
		}
		picked, conflicts, err := local.CherryPick(ctx, c.SHA, c.Parents[0], onto)
		if err != nil {
			return "", "", err
		}
		if len(conflicts) > 0 {
			return "", fmt.Sprintf("%s conflicts in %s", gitk8s.Short(c.SHA), strings.Join(conflicts, ", ")), nil
		}
		if picked == tree {
			continue
		}
		if problem := copyProblem(c); problem != "" {
			return "", problem, nil
		}
		when = max(c.Time, when)
		onto, err = local.WriteCommit(ctx, git.NewCommit{
			Tree:      picked,
			Parents:   []string{onto},
			Author:    c.Author,
			Committer: m.committer(when),
			Message:   c.Message,
		})
		if err != nil {
			return "", "", err
		}
		tree = picked
	}
	if head := log[len(log)-1]; tree != head.Tree {
		return "", "merge commits in the branch change files, and a rebase leaves merges out", nil
	}
	return onto, "", nil
}

// copyProblem says why a new commit can't take c's author, or returns "".
// git refuses a name with only spaces, control characters, and ,:;<>"\',
// and Log gives a name or a date that git can't read as "".
func copyProblem(c git.LogEntry) string {
	name := c.Author.Name
	switch {
	case name == "":
		return fmt.Sprintf("%s's author has no name", gitk8s.Short(c.SHA))
	case !strings.ContainsFunc(name, func(r rune) bool { return r > ' ' && !strings.ContainsRune(`,:;<>"\'`, r) }):
		return fmt.Sprintf("%s's author has no name that git accepts, only %q", gitk8s.Short(c.SHA), name)
	case c.Author.Date == "":
		return fmt.Sprintf("%s's author has no date that git can read", gitk8s.Short(c.SHA))
	}
	return ""
}

// committer returns the merge controller's identity at a time. The times of
// the commits that it makes come from the commits that it copies, so making
// them again gives the same SHAs.
func (m *merger) committer(unix int64) git.Signature {
	return git.Signature{Name: m.ident.Name, Email: m.ident.Email, Date: fmt.Sprintf("%d +0000", unix)}
}

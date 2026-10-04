package main

import (
	"context"
	"fmt"
	"maps"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// syncedPrefix starts the refs in the mirror that hold the heads where the
// mirror and the external repository last synced.
const syncedPrefix = "refs/git-k8s/synced/heads/"

// rewinds says which sides of a diverged branch rewound since the sides
// last synced at synced: "branch" if the branch's head doesn't contain
// synced, because the branch removed commits, "external" if the external
// repository's head doesn't, "both", or "" if neither rewound.
func rewinds(ctx context.Context, repo *git.Repo, head, external, synced string) (string, error) {
	branch, err := repo.IsAncestor(ctx, synced, head)
	if err != nil {
		return "", err
	}
	ext, err := repo.IsAncestor(ctx, synced, external)
	if err != nil {
		return "", err
	}
	switch {
	case !branch && !ext:
		return "both", nil
	case !branch:
		return "branch", nil
	case !ext:
		return "external", nil
	}
	return "", nil
}

// keeps reports whether moving one side of a diverged branch from other to
// head keeps every change that the side made since the sides last synced
// at synced: head has none of the commits that the side removed, and has
// each commit that the side added, or a replay of it if head doesn't
// contain synced. Unless head contains other and the side didn't rewind,
// or head was built on other after the side rewound, head must also have
// every change that the side made, because a replay can match a commit
// that changes other lines, and another commit can bring back what the
// side removed. The mirror moves one side to the other side's head by
// this rule, so when it holds, the mirror resolves the divergence by
// itself.
func keeps(ctx context.Context, repo *git.Repo, head, other, synced string) (bool, error) {
	if forward, err := repo.IsAncestor(ctx, synced, other); err != nil {
		return false, err
	} else if !forward {
		if ok, err := removedNone(ctx, repo, head, other, synced); err != nil || !ok {
			return false, err
		}
		if ok, err := builtOn(ctx, repo, head, other, synced); err != nil || ok {
			return ok, err
		}
		// Another commit in head can bring back what the side removed.
		return replays(ctx, repo, head, other, synced)
	}
	if ok, err := repo.IsAncestor(ctx, other, head); err != nil || ok {
		return ok, err
	}
	// When neither side rewound, only a head that contains other keeps its
	// changes, because replays would rewrite history that didn't rewind.
	if ok, err := repo.IsAncestor(ctx, synced, head); err != nil || ok {
		return false, err
	}
	return replays(ctx, repo, head, other, synced)
}

// replays reports whether head has every change from synced to other, and
// a replay of each commit that other added since synced. A patch ID
// ignores where in a file a change is, so a replay alone doesn't show that
// head has the change.
func replays(ctx context.Context, repo *git.Repo, head, other, synced string) (bool, error) {
	if ok, err := keepsChanges(ctx, repo, head, synced, other); err != nil || !ok {
		return false, err
	}
	missing, _, err := unreplayed(ctx, repo, head, other, synced)
	return err == nil && len(missing) == 0, err
}

// keepsChanges reports whether head has every change from synced to each
// of sides: merging a side into head with synced as the merge base has no
// conflicts and leaves head's tree as it is.
func keepsChanges(ctx context.Context, repo *git.Repo, head, synced string, sides ...string) (bool, error) {
	c, err := repo.Commit(ctx, head)
	if err != nil {
		return false, err
	}
	for _, side := range sides {
		tree, conflicts, err := repo.Merge(ctx, head, side, git.MergeOptions{Base: synced})
		if err != nil || len(conflicts) > 0 || tree != c.Tree {
			return false, err
		}
	}
	return true, nil
}

// builtOn reports whether each commit in head but not in side, a head that
// rewound since synced, was made on top of side, and side has a commit
// that synced doesn't. Then whoever made head started from side after it
// rewound, so head keeps the side's changes even if it changed them to
// resolve conflicts. A side that rewound to an older commit doesn't count:
// a head that contains it can have been made before it rewound.
func builtOn(ctx context.Context, repo *git.Repo, head, side, synced string) (bool, error) {
	if ok, err := repo.IsAncestor(ctx, side, synced); err != nil || ok {
		return false, err
	}
	if ok, err := repo.IsAncestor(ctx, side, head); err != nil || !ok {
		return false, err
	}
	revs, err := repo.Revs(ctx, head, side)
	if err != nil {
		return false, err
	}
	on := map[string]bool{side: true}
	for _, r := range revs {
		if !slices.ContainsFunc(r.Parents, func(p string) bool { return on[p] }) {
			return false, nil
		}
		on[r.Commit] = true
	}
	return true, nil
}

// removedNone reports whether head has none of the commits that side
// removed since synced, which are in synced but not in side. The commits
// that head and synced share are their merge bases and the merge bases'
// ancestors, so side must contain each merge base.
func removedNone(ctx context.Context, repo *git.Repo, head, side, synced string) (bool, error) {
	bases, err := repo.MergeBases(ctx, head, synced)
	if err != nil {
		return false, err
	}
	for _, b := range bases {
		if ok, err := repo.IsAncestor(ctx, b, side); err != nil || !ok {
			return false, err
		}
	}
	return true, nil
}

// unreplayed returns the commits that other added since synced, which are
// in other but not in synced, that head neither has nor has a replay of,
// oldest first. A replay is a commit in head but not in other that removes
// and adds the same lines in the same files, ignoring the unchanged lines
// around them. A merge commit, and a commit that changes no file, have no
// replay. It also returns the patch ID of each commit that other added.
func unreplayed(ctx context.Context, repo *git.Repo, head, other, synced string) ([]git.Rev, map[string]string, error) {
	added, err := repo.Revs(ctx, other, head, synced)
	if err != nil || len(added) == 0 {
		return nil, nil, err
	}
	own, err := repo.Revs(ctx, head, other)
	if err != nil {
		return nil, nil, err
	}
	var commits []string
	for _, r := range added {
		commits = append(commits, r.Commit)
	}
	for _, r := range own {
		if len(r.Parents) <= 1 {
			commits = append(commits, r.Commit)
		}
	}
	ids, err := repo.PatchIDs(ctx, commits)
	if err != nil {
		return nil, nil, err
	}
	replayed := map[string]bool{}
	for _, r := range own {
		if id := ids[r.Commit]; id != "" && len(r.Parents) <= 1 {
			replayed[id] = true
		}
	}
	var missing []git.Rev
	for _, r := range added {
		if id := ids[r.Commit]; id == "" || !replayed[id] {
			missing = append(missing, r)
		}
	}
	return missing, ids, nil
}

// resolveRewind resolves a divergence in which a side of the branch
// rewound since the sides last synced at t.synced. A commit that contains
// both heads brings back the commits that the rewound side removed, so
// the check never merges the heads. It replays the commits that the other
// side added since t.synced onto the rewound side's head instead, and
// pushes the result to the branch.
func resolveRewind(ctx context.Context, in *checks.Input, repo *git.Repo, t target, rewound string, outputs map[string]string) checks.Verdict {
	head := in.Spec.Head
	since := gitk8s.Short(t.synced)
	switch ok, err := keeps(ctx, repo, head, t.commit, t.synced); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return checks.Pass("the branch keeps every change that %s at %s made since they last synced at %s", t.name, gitk8s.Short(t.commit), since)
	}
	switch ok, err := keeps(ctx, repo, t.commit, head, t.synced); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return checks.Pass("%s at %s keeps every change that the branch made since they last synced at %s", t.name, gitk8s.Short(t.commit), since)
	}
	switch rewound {
	case "external":
		return replayBranch(ctx, in, repo, t, rewound, outputs)
	case "branch":
		return replayExternal(ctx, in, repo, t)
	}
	// When both sides rewound, each side's replay onto the other side's
	// head must also leave out the commits that the other side removed.
	switch ok, err := removedNone(ctx, repo, t.commit, head, t.synced); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return replayBranch(ctx, in, repo, t, rewound, outputs)
	}
	switch ok, err := removedNone(ctx, repo, head, t.commit, t.synced); {
	case err != nil:
		return retry(ctx, "%v", err)
	case ok:
		return replayExternal(ctx, in, repo, t)
	}
	return checks.Fail("the branch and %s both rewound since they last synced at %s, and each kept commits that the other removed, so the check leaves the divergence for a person", t.name, since)
}

// parentRewind returns the state and message of the result for branch, a
// branch without a parent whose divergence d has a side that rewound since
// the sides last synced. A commit that contains both heads brings back the
// commits that the rewound side removed, and the merge controller moves
// branch only to a commit that contains its head, so the check pushes
// nothing, and says how to resolve the divergence in the external
// repository instead.
func parentRewind(ctx context.Context, repo *git.Repo, branch, head string, d *gitk8s.Divergence, rewound string) (state, msg string, err error) {
	ext, since := gitk8s.Short(d.Commit), gitk8s.Short(d.Base)
	switch ok, err := keeps(ctx, repo, head, d.Commit, d.Base); {
	case err != nil:
		return "", "", err
	case ok:
		return gitk8s.Passed, fmt.Sprintf("%s keeps every change that the external repository's head %s made since they last synced at %s", branch, ext, since), nil
	}
	switch ok, err := keeps(ctx, repo, d.Commit, head, d.Base); {
	case err != nil:
		return "", "", err
	case ok:
		return gitk8s.Passed, fmt.Sprintf("the external repository's head %s keeps every change that %s made since they last synced at %s", ext, branch, since), nil
	}
	switch rewound {
	case "external":
		msg = fmt.Sprintf("the external repository rewound %s since it last synced with git-k8s at %s, and the merge controller moves %s only to a commit that contains its head, so only the external repository can resolve the divergence: push a head there that replays each commit that landed on %s since %s unchanged, or that contains %s's head %s",
			branch, since, branch, branch, since, branch, gitk8s.Short(head))
	case "branch":
		msg = fmt.Sprintf("%s rewound in git-k8s since it last synced with the external repository at %s; replay the commits that the external repository added since then onto %s's head %s, and push the result to the external repository with a lease on its head %s",
			branch, since, branch, gitk8s.Short(head), ext)
	default:
		msg = fmt.Sprintf("%s rewound both in git-k8s and in the external repository since they last synced at %s, so the check leaves the divergence for a person", branch, since)
	}
	return gitk8s.Failed, msg, nil
}

// replayBranch replays the commits that the branch added since t.synced
// onto the external repository's head, which rewound since then. It
// replays them one at a time, and skips a commit whose replay changes
// nothing, such as one whose change the external repository's head
// already has. When a commit can't be replayed by itself, such as a merge
// or a commit whose replay conflicts, or when the replays don't have
// every change that both sides made, resolve replays all of them as one
// commit, unless the branch rewound too.
func replayBranch(ctx context.Context, in *checks.Input, repo *git.Repo, t target, rewound string, outputs map[string]string) checks.Verdict {
	since := gitk8s.Short(t.synced)
	added, err := repo.Revs(ctx, in.Spec.Head, t.synced, t.commit)
	if err != nil {
		return retry(ctx, "listing the branch's commits since %s: %v", since, err)
	}
	tip, replays, why, err := replayOnto(ctx, repo, t.commit, added, in.Identity, "the branch", false)
	if err != nil {
		return retry(ctx, "replaying the branch's commits onto %s: %v", t.name, err)
	}
	if why == "" {
		// Commits that the branch removed have no replay to leave out.
		switch ok, err := keepsChanges(ctx, repo, tip, t.synced, in.Spec.Head, t.commit); {
		case err != nil:
			return retry(ctx, "comparing the replays of the branch's commits: %v", err)
		case !ok:
			why = "the replays of the branch's commits onto " + t.name + " don't have every change that both sides made"
		}
	}
	switch {
	case why == "" && len(replays) == 0:
		v := checks.Fail("%s rewound since it last synced at %s, and already has every change that the branch made since then", t.name, since)
		v.Fix = t.commit
		return v
	case why == "":
		v := checks.Fail("%s rewound since it last synced at %s; replayed the branch's commits since then onto it", t.name, since)
		if len(replays) < len(added) {
			v.Message += ", skipping those whose changes it already has"
		}
		v.Fix = tip
		return v
	case rewound == "both":
		return checks.Fail("the branch and %s both rewound since they last synced at %s, and %s, so the check leaves the divergence for a person", t.name, since, why)
	}
	t.replay = true
	v := resolve(ctx, in, repo, t, outputs)
	v.Message = why + "; " + v.Message
	return v
}

// replayExternal replays the commits that the external repository added
// since t.synced onto the branch's head, which rewound since then. The
// mirror moves the external repository to the result only if it has a
// replay of each of those commits and every change that they made, so the
// check replays each one unchanged, or fails.
func replayExternal(ctx context.Context, in *checks.Input, repo *git.Repo, t target) checks.Verdict {
	since := gitk8s.Short(t.synced)
	leave := func(why string) checks.Verdict {
		return checks.Fail("the branch rewound since it last synced at %s, and %s, so the check leaves the divergence for a person", since, why)
	}
	missing, ids, err := unreplayed(ctx, repo, in.Spec.Head, t.commit, t.synced)
	if err != nil {
		return retry(ctx, "listing the commits that %s added since %s: %v", t.name, since, err)
	}
	for _, r := range missing {
		if len(r.Parents) == 1 && ids[r.Commit] == "" {
			return leave(fmt.Sprintf("commit %s of %s changes no file, so it has no replay", gitk8s.Short(r.Commit), t.name))
		}
	}
	tip, replays, why, err := replayOnto(ctx, repo, in.Spec.Head, missing, in.Identity, t.name, true)
	switch {
	case err != nil:
		return retry(ctx, "replaying the commits of %s onto the branch: %v", t.name, err)
	case why != "":
		return leave(why)
	}
	got, err := repo.PatchIDs(ctx, slices.Collect(maps.Values(replays)))
	if err != nil {
		return retry(ctx, "comparing the replays of the commits of %s: %v", t.name, err)
	}
	for _, r := range missing {
		if got[replays[r.Commit]] != ids[r.Commit] {
			return leave(fmt.Sprintf("the replay of commit %s of %s doesn't change the same lines in the same files as the commit", gitk8s.Short(r.Commit), t.name))
		}
	}
	switch ok, err := keepsChanges(ctx, repo, tip, t.synced, t.commit); {
	case err != nil:
		return retry(ctx, "comparing the replays of the commits of %s: %v", t.name, err)
	case !ok:
		return leave(fmt.Sprintf("the branch with replays of the commits of %s doesn't have every change that %s made", t.name, t.name))
	}
	v := checks.Fail("the branch rewound since it last synced at %s; replayed the commits that %s added since then onto it", since, t.name)
	v.Fix = tip
	return v
}

// replayOnto replays commits onto onto, in order, with id as the
// committer, and returns the last replay, or onto if it made none, and the
// replay of each commit. Each replay applies its commit's change from the
// commit's parent. A replay that changes nothing stops the replays if
// exact is set, and is skipped otherwise. replayOnto also stops at a
// commit that it can't replay, and says why: a merge, a commit without a
// parent, or a commit whose replay conflicts. side names the commits'
// side of the branch.
func replayOnto(ctx context.Context, repo *git.Repo, onto string, commits []git.Rev, id git.Identity, side string, exact bool) (tip string, replays map[string]string, why string, err error) {
	c, err := repo.Commit(ctx, onto)
	if err != nil {
		return "", nil, "", err
	}
	tip, tree, replays := onto, c.Tree, map[string]string{}
	for _, r := range commits {
		name := fmt.Sprintf("commit %s of %s", gitk8s.Short(r.Commit), side)
		switch len(r.Parents) {
		case 0:
			return tip, replays, name + " has no parent to replay its change from", nil
		case 1:
		default:
			return tip, replays, name + " is a merge, which has no replay", nil
		}
		next, conflicts, err := repo.Merge(ctx, tip, r.Commit, git.MergeOptions{Base: r.Parents[0]})
		if err != nil {
			return "", nil, "", err
		}
		if len(conflicts) > 0 {
			paths := make([]string, len(conflicts))
			for i, c := range conflicts {
				paths[i] = c.Path
			}
			return tip, replays, fmt.Sprintf("replaying %s conflicts in %s", name, strings.Join(paths, ", ")), nil
		}
		if next == tree {
			if exact {
				return tip, replays, "replaying " + name + " changes nothing", nil
			}
			continue
		}
		if tip, err = repo.Replay(ctx, r.Commit, tip, next, id); err != nil {
			return "", nil, "", err
		}
		tree, replays[r.Commit] = next, tip
	}
	return tip, replays, "", nil
}

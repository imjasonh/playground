package git

import (
	"context"
	"slices"
	"strings"
)

// Keeps reports whether head keeps every change that one side of a branch
// made since the two sides last agreed at base. side is that side's head:
// the side removed the commits in base but not in side, and added the
// commits in side but not in base. head keeps those changes when it has
// none of the removed commits and no replay of one, each added commit or a
// replay of it, and every change that the side made since base: merging
// side into head, with base as the merge base, is clean and changes
// nothing.
//
// A replay is a commit in head but not in side that removes and adds the
// same lines in the same files, ignoring whitespace and where in each file
// the lines are. Each commit in head replays at most one commit, and a
// merge commit, or a commit that changes no file, has no replay. head can
// have a replay of a removed commit if an added commit makes the same
// change, as after a rebase. When side and head both contain base, neither
// rewound, so head must contain side: a replay would rewrite history that
// didn't rewind.
//
// A head built on a side that rewound to a new commit keeps that side's
// changes even where it resolved conflicts with them, because whoever made
// head started from the side after it rewound. In that case, merging
// either side or the commit where side and base meet, their only merge
// base, into head, with base as the merge base, must be clean and change
// nothing, so that head brings back no change that the side removed.
//
// An empty head or side means that the branch doesn't exist on that side,
// and an empty base means that the sides never agreed. head, side, and
// base differ.
func (r *Repo) Keeps(ctx context.Context, head, side, base string) (bool, error) {
	k := (*keeper)(r)
	switch {
	case base == "":
		return k.isAncestor(ctx, side, head)
	case head == "":
		return k.isAncestor(ctx, side, base)
	case side == "":
		bases, err := k.mergeBases(ctx, head, base)
		return len(bases) == 0, err
	}
	switch forward, err := k.isAncestor(ctx, base, side); {
	case err != nil:
		return false, err
	case forward:
		if ok, err := k.isAncestor(ctx, side, head); err != nil || ok {
			return ok, err
		}
		if ok, err := k.isAncestor(ctx, base, head); err != nil || ok {
			return false, err
		}
	default:
		if ok, err := k.removedNone(ctx, head, side, base); err != nil || !ok {
			return false, err
		}
		switch built, err := k.builtOn(ctx, head, side, base); {
		case err != nil:
			return false, err
		case built:
			return k.leavesOut(ctx, head, side, base)
		}
	}
	// The merge runs first because it's cheap: the replays hash the commits
	// that head has and side doesn't, which after a rebase can be all of
	// main's new commits.
	if ok, err := k.changes(ctx, head, side, base); err != nil || !ok {
		return false, err
	}
	return k.replays(ctx, head, side, base)
}

// keeper runs the git commands that Keeps needs.
type keeper Repo

// exec runs git in the repository. It limits git to the transports that a
// GitRepository's URL can name, even though these commands read only local
// objects, because a repository with a promisor remote fetches the objects
// that it lacks.
func (k *keeper) exec(ctx context.Context, stdin []byte, args ...string) (result, error) {
	return k.git.exec(ctx, k.Dir, args, opts{stdin: stdin, env: []string{"GIT_ALLOW_PROTOCOL=http:https:git:ssh"}})
}

// noAttributes returns the option that makes git read attributes from the
// empty tree. Without it, git reads them from the tree that attr.tree names
// or, in some versions such as 2.43, from HEAD in a bare repository, and a
// .gitattributes file there changes what Keeps says about every branch.
func (k *keeper) noAttributes(ctx context.Context) (string, error) {
	empty, err := k.run(ctx, []byte{}, "hash-object", "-t", "tree", "--stdin")
	return "--attr-source=" + strings.TrimSpace(string(empty)), err
}

func (k *keeper) run(ctx context.Context, stdin []byte, args ...string) ([]byte, error) {
	res, err := k.exec(ctx, stdin, args...)
	if err == nil && res.code != 0 {
		err = &Error{Command: args[0], Code: res.code, Stderr: res.stderr}
	}
	return res.stdout, err
}

func (k *keeper) isAncestor(ctx context.Context, ancestor, descendant string) (bool, error) {
	res, err := k.exec(ctx, nil, "merge-base", "--is-ancestor", "--end-of-options", ancestor, descendant)
	switch {
	case err != nil:
		return false, err
	case res.code == 0:
		return true, nil
	case res.code == 1:
		return false, nil
	}
	return false, &Error{Command: "merge-base", Code: res.code, Stderr: res.stderr}
}

// mergeBases returns the best common ancestors of a and b, or none if they
// have no common ancestor.
func (k *keeper) mergeBases(ctx context.Context, a, b string) ([]string, error) {
	res, err := k.exec(ctx, nil, "merge-base", "--all", "--end-of-options", a, b)
	switch {
	case err != nil:
		return nil, err
	case res.code == 0:
		return strings.Fields(string(res.stdout)), nil
	case res.code == 1:
		return nil, nil
	}
	return nil, &Error{Command: "merge-base", Code: res.code, Stderr: res.stderr}
}

// removedNone reports whether head has none of the commits that the side
// removed, which are in base but not in side, and no replay of one, unless
// a commit that the side added makes the same change. The commits that
// head and base share are their merge bases and the merge bases'
// ancestors, so side must contain each merge base. The merges can't see a
// replay of a removed commit whose change other removed commits undid,
// such as a secret and its revert that a force push purged.
func (k *keeper) removedNone(ctx context.Context, head, side, base string) (bool, error) {
	bases, err := k.mergeBases(ctx, head, base)
	if err != nil {
		return false, err
	}
	for _, b := range bases {
		if ok, err := k.isAncestor(ctx, b, side); err != nil || !ok {
			return false, err
		}
	}
	removed, err := k.revs(ctx, base, side, nil)
	if err != nil || len(removed) == 0 {
		return err == nil, err
	}
	own, err := k.revs(ctx, head, side, nil)
	if err != nil || len(own) == 0 {
		return err == nil, err
	}
	// Two commits make the same change only if they change the same
	// files, so Keeps hashes only the commits that change a file that the
	// shorter list changes.
	shorter := removed
	if len(own) < len(removed) {
		shorter = own
	}
	paths, err := k.files(ctx, shorter)
	if err != nil || len(paths) == 0 {
		return err == nil, err
	}
	var ids [3]map[string]bool
	for i, r := range [][2]string{{base, side}, {side, base}, {head, side}} {
		if ids[i], err = k.patches(ctx, r[0], r[1], paths); err != nil {
			return false, err
		}
	}
	gone, readded, copies := ids[0], ids[1], ids[2]
	for id := range copies {
		if gone[id] && !readded[id] {
			return false, nil
		}
	}
	return true, nil
}

// revs lists the commits in a but not in b, other than merge commits, that
// change a file in paths, or any file if paths is nil. It lists a commit
// on a side of a merge even if the merge's result doesn't have its change.
func (k *keeper) revs(ctx context.Context, a, b string, paths []string) ([]string, error) {
	args := []string{"rev-list", "--no-merges", "--full-history", "--end-of-options", a, "^" + b, "--"}
	if paths == nil {
		out, err := k.run(ctx, nil, args...)
		return strings.Fields(string(out)), err
	}
	var commits []string
	seen := map[string]bool{}
	// Chunks keep the command line short.
	for chunk := range slices.Chunk(paths, 1000) {
		spec := slices.Clone(args)
		for _, p := range chunk {
			spec = append(spec, ":(literal)"+p)
		}
		out, err := k.run(ctx, nil, spec...)
		if err != nil {
			return nil, err
		}
		for _, c := range strings.Fields(string(out)) {
			if !seen[c] {
				seen[c] = true
				commits = append(commits, c)
			}
		}
	}
	return commits, nil
}

// patches returns the patch IDs of the changes of the commits that revs
// lists, other than commits that change no file.
func (k *keeper) patches(ctx context.Context, a, b string, paths []string) (map[string]bool, error) {
	commits, err := k.revs(ctx, a, b, paths)
	if err != nil || len(commits) == 0 {
		return nil, err
	}
	m, err := k.changeIDs(ctx, commits)
	ids := map[string]bool{}
	for _, id := range m {
		if id != "" {
			ids[id] = true
		}
	}
	return ids, err
}

// files returns the paths of the files that commits change, sorted, so
// that each chunk of paths that revs passes to git covers one contiguous
// part of the tree, and git skips the directories outside it when it
// compares a commit with its parent.
func (k *keeper) files(ctx context.Context, commits []string) ([]string, error) {
	out, err := k.run(ctx, []byte(strings.Join(commits, "\n")+"\n"), "diff-tree", "--stdin", "--root", "-r", "--no-commit-id", "--name-only", "-z")
	if err != nil {
		return nil, err
	}
	var paths []string
	seen := map[string]bool{}
	for p := range strings.SplitSeq(string(out), "\x00") {
		if p != "" && !seen[p] {
			seen[p] = true
			paths = append(paths, p)
		}
	}
	slices.Sort(paths)
	return paths, nil
}

// builtOn reports whether side rewound to a new commit, which base doesn't
// have, and each commit in head but not in side was made on top of side or
// on top of another such commit. A side that rewound to an older commit
// doesn't count, because a head that contains it can have been made before
// it rewound.
func (k *keeper) builtOn(ctx context.Context, head, side, base string) (bool, error) {
	if ok, err := k.isAncestor(ctx, side, base); err != nil || ok {
		return false, err
	}
	if ok, err := k.isAncestor(ctx, side, head); err != nil || !ok {
		return false, err
	}
	out, err := k.run(ctx, nil, "rev-list", "--reverse", "--topo-order", "--parents", "--end-of-options", head, "^"+side)
	if err != nil {
		return false, err
	}
	on := map[string]bool{side: true}
	for line := range strings.Lines(string(out)) {
		f := strings.Fields(line)
		if len(f) == 0 {
			continue
		}
		if !slices.ContainsFunc(f[1:], func(p string) bool { return on[p] }) {
			return false, nil
		}
		on[f[0]] = true
	}
	return true, nil
}

// leavesOut reports whether head, which was built on side, has none of the
// changes that the side removed. Either of two merges, each with base as
// the merge base, shows it when it's clean and changes nothing, and each
// can pass where the other conflicts:
//
//   - Merging side conflicts where head resolved conflicts with the side's
//     changes.
//   - Merging the commit where side and base meet, their only merge base,
//     conflicts where the side's new commits changed lines that the
//     removed commits changed.
func (k *keeper) leavesOut(ctx context.Context, head, side, base string) (bool, error) {
	if ok, err := k.changes(ctx, head, side, base); err != nil || ok {
		return ok, err
	}
	bases, err := k.mergeBases(ctx, side, base)
	if err != nil || len(bases) != 1 {
		return false, err
	}
	return k.changes(ctx, head, bases[0], base)
}

// changes reports whether head has every change from base to side: merging
// side into head, with base as the merge base, is clean and leaves head's
// tree as it is. The merge reads attributes from the empty tree, so that no
// .gitattributes file, such as one that union-merges a file, can change how
// it merges.
func (k *keeper) changes(ctx context.Context, head, side, base string) (bool, error) {
	noAttrs, err := k.noAttributes(ctx)
	if err != nil {
		return false, err
	}
	res, err := k.exec(ctx, nil, noAttrs,
		"merge-tree", "--write-tree", "--no-messages", "--merge-base="+base, "--end-of-options", head, side)
	switch {
	case err != nil:
		return false, err
	case res.code == 1:
		return false, nil
	case res.code != 0:
		return false, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
	}
	tree, _, _ := strings.Cut(string(res.stdout), "\n")
	headTree, err := k.run(ctx, nil, "rev-parse", "--verify", "--end-of-options", head+"^{tree}")
	return err == nil && tree == strings.TrimSpace(string(headTree)), err
}

// replays reports whether head has a replay of each commit in side but not
// in head or base. rev-list lists the newest commits first, and replays are
// usually the newest, so it hashes head's commits in growing batches and
// stops once each commit has a replay: head can hold thousands of commits
// that side doesn't, such as a main branch that it was rebased onto.
func (k *keeper) replays(ctx context.Context, head, side, base string) (bool, error) {
	out, err := k.run(ctx, nil, "rev-list", "--end-of-options", side, "^"+head, "^"+base)
	if err != nil {
		return false, err
	}
	commits := strings.Fields(string(out))
	if len(commits) == 0 {
		return true, nil
	}
	need, err := k.changeIDs(ctx, commits)
	if err != nil {
		return false, err
	}
	missing := map[string]int{}
	for _, c := range commits {
		if need[c] == "" {
			return false, nil
		}
		missing[need[c]]++
	}
	out, err = k.run(ctx, nil, "rev-list", "--no-merges", "--end-of-options", head, "^"+side)
	if err != nil {
		return false, err
	}
	have := strings.Fields(string(out))
	for n := 64; len(have) > 0 && len(missing) > 0; n *= 2 {
		batch := have[:min(n, len(have))]
		have = have[len(batch):]
		ids, err := k.changeIDs(ctx, batch)
		if err != nil {
			return false, err
		}
		for _, c := range batch {
			if id := ids[c]; missing[id] > 1 {
				missing[id]--
			} else {
				delete(missing, id)
			}
		}
	}
	return len(missing) == 0, nil
}

// changeIDs maps each commit to the patch ID of its change from its parent,
// computed from a diff without context lines. A merge commit, which
// diff-tree doesn't diff, and a commit that changes no file map to "".
// patch-id identifies a binary file's change by the blobs' full names,
// which --full-index prints, so the diff needn't carry the files' contents.
// The diff reads attributes from the empty tree, so that no .gitattributes
// file, such as one that marks text files binary, can keep a replay from
// matching.
func (k *keeper) changeIDs(ctx context.Context, commits []string) (map[string]string, error) {
	noAttrs, err := k.noAttributes(ctx)
	if err != nil {
		return nil, err
	}
	res, err := k.exec(ctx, []byte(strings.Join(commits, "\n")+"\n"), noAttrs,
		"diff-tree", "--stdin", "--root", "-p", "-U0", "--full-index")
	if err == nil && res.code != 0 {
		err = &Error{Command: "diff-tree", Code: res.code, Stderr: res.stderr}
	}
	if err != nil {
		return nil, err
	}
	out, err := k.run(ctx, res.stdout, "patch-id", "--stable")
	if err != nil {
		return nil, err
	}
	ids := make(map[string]string, len(commits))
	for line := range strings.Lines(string(out)) {
		if id, commit, ok := strings.Cut(strings.TrimSpace(line), " "); ok {
			ids[commit] = id
		}
	}
	return ids, nil
}

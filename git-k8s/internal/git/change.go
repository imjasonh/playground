package git

import (
	"context"
	"errors"
	"fmt"
	"strings"
)

// Change is what a branch's head changes on top of its merge base with the
// parent's head.
type Change struct {
	// Base is the merge base: the best common ancestor of Head and the
	// parent's head. It's "" when they have no common ancestor, or more
	// than one best one, because then what Head changes isn't defined.
	Base string
	Head string
}

// MaxChangeBytes is the most output that SameChange reads from git for the
// files that one change touches, and that Numstat reads for the files that
// differ between two commits.
const MaxChangeBytes = 8 << 20

// errChangeTooBig is what changedFiles returns when git prints more than
// MaxChangeBytes.
var errChangeTooBig = fmt.Errorf("git diff-tree: more than %d MiB of changed files", MaxChangeBytes>>20)

// SameChange reports whether b makes the same change as a, so that what
// holds for a's change also holds for b's. Two things must be true:
//
//   - Merging a.Head into b.Base, with a.Base as the merge base, is clean
//     and gives b.Head's files, modes included. So b.Head is b.Base with
//     a's change, as git merges it, and nothing else. That's what happens
//     when b.Head merges a newer parent into a.Head, as the base check
//     does, or when b.Head rebases or squashes a.Head without resolving a
//     conflict.
//   - b changes no file that a doesn't, and leaves each file that it
//     changes with the mode that a leaves it with. The merge follows files
//     that the parent renamed since a.Base, so a's change to one file can
//     land in a file with another name, which path-based rules can treat
//     differently. It also keeps a mode that the parent changed, such as
//     an executable bit on a file whose text a changes. b can change fewer
//     files, such as when the parent already has part of a's change.
//
// SameChange is conservative: when it can't tell, it reports that the
// changes differ. That includes a change without a merge base, a merge that
// conflicts, such as where both changes touch the same binary file or
// submodule, and a change whose list of files takes more than
// MaxChangeBytes.
// Attributes from the commits' .gitattributes files don't apply to the
// merge, as with MergeTree, so a branch can't make clean a merge that would
// conflict. SameChange doesn't compare the commits' messages, authors, or
// signatures.
//
// The work doesn't depend on how many commits the changes have: SameChange
// runs at most five git commands, which read the four commits' trees.
func (r *Repo) SameChange(ctx context.Context, a, b Change) (bool, error) {
	switch {
	case a.Base == "" || b.Base == "":
		return false, nil
	case a == b:
		return true, nil
	case !objectNames([]string{a.Base, a.Head, b.Base, b.Head}):
		return false, fmt.Errorf("comparing changes: %q, %q, %q, and %q aren't all object names", a.Base, a.Head, b.Base, b.Head)
	}
	if a.Base == b.Base {
		// Merging a.Head into its own merge base gives a.Head's files.
		ta, err := r.tree(ctx, a.Head)
		if err != nil {
			return false, err
		}
		tb, err := r.tree(ctx, b.Head)
		return err == nil && ta == tb, err
	}
	noAttrs, err := r.noAttributes(ctx)
	if err != nil {
		return false, err
	}
	// A clean merge prints only the tree's name. Anything more lists
	// conflicts, so a little room is enough.
	out := &limitedWriter{n: 1 << 10}
	args := []string{noAttrs, "merge-tree", "--write-tree", "--name-only", "-z", "--no-messages",
		"--merge-base=" + a.Base, "--end-of-options", b.Base, a.Head}
	res, err := r.git.exec(ctx, r.Dir, args, opts{out: out})
	merged, _, _ := strings.Cut(string(out.b), "\x00")
	switch {
	case out.full || err == nil && res.code == 1 && merged != "":
		return false, nil
	case err != nil:
		return false, err
	case res.code != 0:
		return false, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
	}
	tree, err := r.tree(ctx, b.Head)
	if err != nil || merged != tree {
		return false, err
	}
	theirs, err := r.changedFiles(ctx, b)
	if errors.Is(err, errChangeTooBig) {
		return false, nil
	}
	if err != nil || len(theirs) == 0 {
		return err == nil, err
	}
	ours, err := r.changedFiles(ctx, a)
	if errors.Is(err, errChangeTooBig) {
		return false, nil
	}
	if err != nil {
		return false, err
	}
	for p, mode := range theirs {
		if m, ok := ours[p]; !ok || m != mode {
			return false, nil
		}
	}
	return true, nil
}

// IsObjectName reports whether s is a full SHA-1 or SHA-256 object name in
// lowercase hex.
func IsObjectName(s string) bool { return objectNames([]string{s}) }

// tree returns the name of a commit's tree.
func (r *Repo) tree(ctx context.Context, commit string) (string, error) {
	return r.text(ctx, "rev-parse", "--verify", "--end-of-options", commit+"^{tree}")
}

// changedFiles maps the path of each file that c adds, removes, or changes,
// including a file whose mode it changes, to the file's mode at c.Head,
// which is 000000 for a file that c removes. A renamed file is two paths.
func (r *Repo) changedFiles(ctx context.Context, c Change) (map[string]string, error) {
	out := &limitedWriter{n: MaxChangeBytes}
	args := []string{"diff-tree", "-r", "-z", "--no-renames", "--end-of-options", c.Base, c.Head}
	_, err := r.git.run(ctx, r.Dir, args, opts{out: out})
	if out.full {
		return nil, errChangeTooBig
	}
	if err != nil {
		return nil, err
	}
	files := map[string]string{}
	text := strings.TrimSuffix(string(out.b), "\x00")
	if text == "" {
		return files, nil
	}
	// Each file is ":OLDMODE NEWMODE OLDSHA NEWSHA STATUS" and its path.
	fields := strings.Split(text, "\x00")
	for i := 0; i < len(fields); i += 2 {
		info := strings.Fields(fields[i])
		if len(info) != 5 || i+1 == len(fields) {
			return nil, fmt.Errorf("git diff-tree printed %q, which isn't a changed file", fields[i])
		}
		files[fields[i+1]] = info[1]
	}
	return files, nil
}

// FetchCommits fetches commits by name from the remote, such as a commit
// that no branch has anymore, without updating any ref. The remote must
// serve commits that no ref points to, as git's protocol version 2 does.
func (r *Repo) FetchCommits(ctx context.Context, remote Remote, commits ...string) error {
	switch {
	case len(commits) == 0:
		return nil
	case !objectNames(commits):
		return fmt.Errorf("fetching commits: %q aren't all object names", commits)
	}
	args := append([]string{"fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--end-of-options", remote.URL}, commits...)
	_, err := r.git.run(ctx, r.Dir, args, opts{auth: remote.Auth})
	return err
}

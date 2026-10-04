package git

import (
	"context"
	"fmt"
	"strconv"
	"strings"
)

// Rev is a commit and its parents.
type Rev struct {
	Commit  string
	Parents []string
}

// Revs lists the commits in head but not in any of excluded, oldest first,
// with each commit after its parents. An empty excluded commit excludes
// nothing.
func (r *Repo) Revs(ctx context.Context, head string, excluded ...string) ([]Rev, error) {
	args := []string{"rev-list", "--reverse", "--topo-order", "--parents", "--end-of-options", head}
	for _, x := range excluded {
		if x != "" {
			args = append(args, "^"+x)
		}
	}
	out, err := r.git.run(ctx, r.Dir, args, opts{env: remoteProtocols})
	if err != nil {
		return nil, err
	}
	var revs []Rev
	for line := range strings.Lines(string(out)) {
		if f := strings.Fields(line); len(f) > 0 {
			revs = append(revs, Rev{Commit: f[0], Parents: f[1:]})
		}
	}
	return revs, nil
}

// PatchIDs maps each commit to the patch ID of its change from its parent,
// computed from a diff without context lines, so that the ID doesn't
// change when a commit is replayed onto a parent that changed the lines
// around its change. A merge commit, and a commit that changes no file,
// map to "".
func (r *Repo) PatchIDs(ctx context.Context, commits []string) (map[string]string, error) {
	ids := make(map[string]string, len(commits))
	if len(commits) == 0 {
		return ids, nil
	}
	diffs, err := r.git.run(ctx, r.Dir, []string{"diff-tree", "--stdin", "--root", "-p", "-U0", "--full-index"},
		opts{stdin: []byte(strings.Join(commits, "\n") + "\n"), env: remoteProtocols})
	if err != nil {
		return nil, err
	}
	out, err := r.git.run(ctx, r.Dir, []string{"patch-id", "--stable"}, opts{stdin: diffs, env: remoteProtocols})
	if err != nil {
		return nil, err
	}
	for _, c := range commits {
		ids[c] = ""
	}
	for line := range strings.Lines(string(out)) {
		id, commit, ok := strings.Cut(strings.TrimSpace(line), " ")
		if _, want := ids[commit]; ok && want {
			ids[commit] = id
		}
	}
	return ids, nil
}

// Replay commits tree with parent as its only parent, and with the author,
// author date, and message of commit, which it replays. The committer is
// id, at the later of commit's and parent's committer times, so the same
// arguments always make the same commit.
func (r *Repo) Replay(ctx context.Context, commit, parent, tree string, id Identity) (string, error) {
	out, err := r.git.run(ctx, r.Dir, []string{"show", "-s", "--date=raw", "--format=format:%an%x00%ae%x00%ad%x00%ct%x00%B", "--end-of-options", commit},
		opts{env: remoteProtocols})
	if err != nil {
		return "", err
	}
	f := strings.SplitN(string(out), "\x00", 5)
	if len(f) != 5 {
		return "", fmt.Errorf("git show: unexpected output %q", out)
	}
	ct, err := strconv.ParseInt(f[3], 10, 64)
	if err != nil {
		return "", fmt.Errorf("git show: unexpected committer time %q", f[3])
	}
	out, err = r.git.run(ctx, r.Dir, []string{"show", "-s", "--format=format:%ct", "--end-of-options", parent}, opts{env: remoteProtocols})
	if err != nil {
		return "", err
	}
	pct, err := strconv.ParseInt(string(out), 10, 64)
	if err != nil {
		return "", fmt.Errorf("git show: unexpected committer time %q", out)
	}
	env := append([]string{
		"GIT_AUTHOR_NAME=" + f[0], "GIT_AUTHOR_EMAIL=" + f[1], "GIT_AUTHOR_DATE=@" + f[2],
		"GIT_COMMITTER_NAME=" + id.Name, "GIT_COMMITTER_EMAIL=" + id.Email, fmt.Sprintf("GIT_COMMITTER_DATE=@%d +0000", max(ct, pct)),
	}, remoteProtocols...)
	out, err = r.git.run(ctx, r.Dir, []string{"commit-tree", "-p", parent, "-F", "-", "--end-of-options", tree}, opts{stdin: []byte(f[4]), env: env})
	return strings.TrimSpace(string(out)), err
}

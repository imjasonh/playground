package git

import (
	"context"
	"fmt"
	"strconv"
	"strings"
)

// Signature is the author or committer of a commit.
type Signature struct {
	Name  string
	Email string
	// Date is a time in git's raw format: seconds since the Unix epoch and
	// a time zone offset, such as "1700000000 -0800".
	Date string
}

// LogEntry is one commit that Log lists.
type LogEntry struct {
	SHA     string
	Tree    string
	Parents []string
	// Author has "" for a name, an email, or a date that git can't read.
	// Some dates that git reads, such as one with a five-digit time zone,
	// can't go into a new commit unchanged.
	Author Signature
	// Committer is the committer's name and email, and Time is the
	// committer time, in seconds since the Unix epoch, or 0 when git can't
	// read it.
	Committer Identity
	Time      int64
	Message   string
	// Trailers are the trailers at the end of the message, as git parses
	// them, such as "Signed-off-by: Ana Lima <ana@example.com>".
	Trailers []string
}

// Subject returns the first line of the commit's message.
func (e *LogEntry) Subject() string {
	subject, _, _ := strings.Cut(strings.TrimSpace(e.Message), "\n")
	return strings.TrimSpace(subject)
}

// Fixer reports whether a check pushed the commit. Like CountFixerCommits,
// it looks for a line of the message that starts with the fixer trailer.
func (e *LogEntry) Fixer() bool {
	for line := range strings.SplitSeq(e.Message, "\n") {
		if strings.HasPrefix(line, FixerTrailer+":") {
			return true
		}
	}
	return false
}

// MaxLogBytes is the most output that Log reads from git.
const MaxLogBytes = 8 << 20

// ErrLogTooBig is the error from Log when git prints more than
// MaxLogBytes.
var ErrLogTooBig = fmt.Errorf("git log: more than %d MiB of output", MaxLogBytes>>20)

// HasMerge reports whether head has a merge commit that base doesn't have.
func (r *Repo) HasMerge(ctx context.Context, base, head string) (bool, error) {
	out, err := r.text(ctx, "rev-list", "--merges", "--max-count=1", "--end-of-options", head, "^"+base)
	return out != "", err
}

// Parents returns a commit's parents.
func (r *Repo) Parents(ctx context.Context, sha string) ([]string, error) {
	out, err := r.text(ctx, "show", "-s", "--format=%P", "--end-of-options", sha)
	return strings.Fields(out), err
}

// Log lists the commits in head but not in base, including merges, with
// every commit after its parents. It lists at most limit commits, so a
// caller that asks for one more than it wants can tell when there are too
// many. It returns ErrLogTooBig when the commits' names, messages, and
// other fields have more than MaxLogBytes.
func (r *Repo) Log(ctx context.Context, base, head string, limit int) ([]LogEntry, error) {
	args := []string{"log", "-z", "--reverse", "--topo-order", "--date=raw", "--max-count=" + strconv.Itoa(limit),
		"--format=%H%x00%T%x00%P%x00%an%x00%ae%x00%ad%x00%cn%x00%ce%x00%ct%x00%B%x00%(trailers:only,unfold)", "--end-of-options", head, "^" + base}
	out := &limitedWriter{n: MaxLogBytes}
	_, err := r.git.run(ctx, r.Dir, args, opts{stdout: out})
	if out.full {
		// git dies when the write fails, so err doesn't say why.
		return nil, ErrLogTooBig
	}
	if err != nil {
		return nil, err
	}
	// Each commit is 11 fields, each followed by a NUL. git stops printing
	// a name, message, or trailer at a NUL inside it, so a commit can't add
	// fields.
	const n = 11
	fields := strings.Split(string(out.b), "\x00")
	if len(fields)%n != 1 {
		return nil, fmt.Errorf("git log: unexpected output")
	}
	var entries []LogEntry
	for f := fields; len(f) > 1; f = f[n:] {
		parents := strings.Fields(f[2])
		if !objectNames(append([]string{f[0], f[1]}, parents...)) {
			return nil, fmt.Errorf("git log: unexpected commit %q", f[0])
		}
		// git prints a committer time that it can't read as "", but not
		// one that's too big for an int64.
		t, err := strconv.ParseInt(f[8], 10, 64)
		if err != nil {
			t = 0
		}
		entries = append(entries, LogEntry{
			SHA:       f[0],
			Tree:      f[1],
			Parents:   parents,
			Author:    Signature{Name: f[3], Email: f[4], Date: f[5]},
			Committer: Identity{Name: f[6], Email: f[7]},
			Time:      t,
			Message:   f[9],
			Trailers:  strings.FieldsFunc(f[10], func(r rune) bool { return r == '\n' }),
		})
	}
	return entries, nil
}

// limitedWriter keeps up to n bytes, and fails the write that would go
// over. It has only Write, so that io.Copy can't go around the limit with
// ReadFrom.
type limitedWriter struct {
	b    []byte
	n    int
	full bool
}

func (w *limitedWriter) Write(p []byte) (int, error) {
	if len(w.b)+len(p) > w.n {
		w.full = true
		return 0, ErrLogTooBig
	}
	w.b = append(w.b, p...)
	return len(p), nil
}

// objectNames reports whether every string is a SHA-1 or SHA-256 object
// name.
func objectNames(names []string) bool {
	for _, s := range names {
		if (len(s) != 40 && len(s) != 64) || strings.Trim(s, "0123456789abcdef") != "" {
			return false
		}
	}
	return true
}

// CherryPick applies the change from parent to commit on top of onto,
// without a worktree. It returns the resulting tree, or the paths that
// conflict.
func (r *Repo) CherryPick(ctx context.Context, commit, parent, onto string) (tree string, conflicts []string, err error) {
	args := []string{"merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", "--merge-base=" + parent, "--end-of-options", onto, commit}
	res, err := r.git.exec(ctx, r.Dir, args, opts{})
	if err != nil {
		return "", nil, err
	}
	var fields []string
	for f := range strings.SplitSeq(string(res.stdout), "\x00") {
		if f != "" {
			fields = append(fields, f)
		}
	}
	switch {
	case res.code == 0 && len(fields) > 0:
		return fields[0], nil, nil
	case res.code == 1 && len(fields) > 1:
		return "", fields[1:], nil
	}
	return "", nil, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
}

// NewCommit is a commit for WriteCommit to make.
type NewCommit struct {
	Tree      string
	Parents   []string
	Author    Signature
	Committer Signature
	Message   string
}

// WriteCommit makes a commit object and returns its SHA. Unlike CommitTree,
// it sets the author and committer separately, with their time zones.
func (r *Repo) WriteCommit(ctx context.Context, c NewCommit) (string, error) {
	args := []string{"commit-tree"}
	for _, p := range c.Parents {
		args = append(args, "-p", p)
	}
	args = append(args, "-F", "-", "--end-of-options", c.Tree)
	env := []string{
		"GIT_AUTHOR_NAME=" + c.Author.Name, "GIT_AUTHOR_EMAIL=" + c.Author.Email, "GIT_AUTHOR_DATE=@" + c.Author.Date,
		"GIT_COMMITTER_NAME=" + c.Committer.Name, "GIT_COMMITTER_EMAIL=" + c.Committer.Email, "GIT_COMMITTER_DATE=@" + c.Committer.Date,
	}
	out, err := r.git.run(ctx, r.Dir, args, opts{stdin: []byte(c.Message), env: env})
	return strings.TrimSpace(string(out)), err
}

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
	out, err := r.run(ctx, args...)
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
// map to "". The diff reads attributes from the empty tree, so that no
// .gitattributes file, such as one that marks text files binary, can keep
// a replay from matching.
func (r *Repo) PatchIDs(ctx context.Context, commits []string) (map[string]string, error) {
	ids := make(map[string]string, len(commits))
	if len(commits) == 0 {
		return ids, nil
	}
	noAttrs, err := r.noAttributes(ctx)
	if err != nil {
		return nil, err
	}
	res, err := r.git.exec(ctx, r.Dir, []string{noAttrs, "diff-tree", "--stdin", "--root", "-p", "-U0", "--full-index"},
		opts{stdin: []byte(strings.Join(commits, "\n") + "\n")})
	if err == nil && res.code != 0 {
		err = &Error{Command: "diff-tree", Code: res.code, Stderr: res.stderr}
	}
	if err != nil {
		return nil, err
	}
	out, err := r.git.run(ctx, r.Dir, []string{"patch-id", "--stable"}, opts{stdin: res.stdout})
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
	out, err := r.run(ctx, "show", "-s", "--date=raw", "--format=format:%an%x00%ae%x00%ad%x00%ct%x00%B", "--end-of-options", commit)
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
	out, err = r.run(ctx, "show", "-s", "--format=format:%ct", "--end-of-options", parent)
	if err != nil {
		return "", err
	}
	pct, err := strconv.ParseInt(string(out), 10, 64)
	if err != nil {
		return "", fmt.Errorf("git show: unexpected committer time %q", out)
	}
	return r.WriteCommit(ctx, NewCommit{
		Tree:      tree,
		Parents:   []string{parent},
		Author:    Signature{Name: f[0], Email: f[1], Date: f[2]},
		Committer: Signature{Name: id.Name, Email: id.Email, Date: fmt.Sprintf("%d +0000", max(ct, pct))},
		Message:   f[4],
	})
}

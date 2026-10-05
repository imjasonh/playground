// Package git runs the git command-line tool.
//
// Controllers keep git objects in local bare repositories and run git
// against them. Only commit SHAs go into Kubernetes objects.
package git

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync/atomic"
	"time"
	"unicode/utf8"
)

// FixerTrailer is the commit trailer that marks commits pushed by checks.
const FixerTrailer = "Git-K8s-Fixer"

// AgentTrailer is the commit trailer that marks commits with changes that
// an AI agent made.
const AgentTrailer = "Git-K8s-Agent"

// AllowProtocol is the GIT_ALLOW_PROTOCOL setting that git-k8s runs git
// with. It allows only the transports that a GitRepository's URL can name.
// It leaves out file, which also covers plain paths, so git can't read a
// local repository such as another GitRepository's cache.
const AllowProtocol = "http:https:git:ssh"

// Auth is a username and password for HTTP basic authentication.
type Auth struct {
	Username string
	Password string
}

// Remote is a remote repository's URL and credentials.
type Remote struct {
	URL  string
	Auth *Auth
}

// Identity is the author and committer of commits that controllers make.
type Identity struct {
	Name  string
	Email string
}

// Written returns the identity as git writes it in a commit. git drops
// spaces, ASCII control characters other than DEL, and ,:;<>"\' from the
// start and the end of the name and the email, and <, >, and newlines from
// the rest. Then it reads each byte that isn't part of valid UTF-8 as
// Latin-1, and treats the bytes of noncharacters, such as U+FFFE, the same
// way.
func (id Identity) Written() Identity {
	return Identity{Name: written(id.Name), Email: written(id.Email)}
}

func written(s string) string {
	s = strings.TrimFunc(s, func(r rune) bool { return r <= ' ' || strings.ContainsRune(`,:;<>"\'`, r) })
	s = strings.NewReplacer("\n", "", "<", "", ">", "").Replace(s)
	var b strings.Builder
	for len(s) > 0 {
		r, n := utf8.DecodeRuneInString(s)
		if r == utf8.RuneError && n == 1 || r&0xfffe == 0xfffe || r >= 0xfdd0 && r <= 0xfdef {
			r, n = rune(s[0]), 1
		}
		b.WriteRune(r)
		s = s[n:]
	}
	return b.String()
}

// Git runs git commands. The zero value runs "git" from PATH with a
// 5-minute timeout per command.
type Git struct {
	// Bin is the git executable. It defaults to "git".
	Bin string
	// Timeout limits each command. It defaults to 5 minutes.
	Timeout time.Duration
}

// Error is a git command that failed.
type Error struct {
	Command string
	Code    int
	Stderr  string
}

func (e *Error) Error() string {
	if e.Stderr == "" {
		return fmt.Sprintf("git %s: exit status %d", e.Command, e.Code)
	}
	return fmt.Sprintf("git %s: exit status %d: %s", e.Command, e.Code, e.Stderr)
}

type opts struct {
	auth  *Auth
	stdin []byte
	env   []string
	// stdout takes the command's output instead of result.stdout.
	stdout io.Writer
}

type result struct {
	code   int
	stdout []byte
	stderr string
}

func (g *Git) exec(ctx context.Context, dir string, args []string, o opts) (result, error) {
	bin := g.Bin
	if bin == "" {
		bin = "git"
	}
	timeout := g.Timeout
	if timeout == 0 {
		timeout = 5 * time.Minute
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	if dir != "" {
		args = append([]string{"-C", dir}, args...)
	}
	cmd := exec.CommandContext(ctx, bin, args...)
	env := []string{
		// Never prompt, and ignore system and user configuration so that
		// results don't depend on the machine.
		"GIT_TERMINAL_PROMPT=0",
		"GIT_CONFIG_NOSYSTEM=1",
		"GIT_CONFIG_GLOBAL=" + os.DevNull,
		"GIT_ALLOW_PROTOCOL=" + AllowProtocol,
		"LC_ALL=C",
	}
	for _, kv := range os.Environ() {
		if !strings.HasPrefix(kv, "GIT_") && !strings.HasPrefix(kv, "LC_ALL=") {
			env = append(env, kv)
		}
	}
	if o.auth != nil {
		// Pass the header in the environment, not argv, so it doesn't show
		// up in process listings.
		token := base64.StdEncoding.EncodeToString([]byte(o.auth.Username + ":" + o.auth.Password))
		env = append(env, "GIT_CONFIG_COUNT=1", "GIT_CONFIG_KEY_0=http.extraHeader",
			"GIT_CONFIG_VALUE_0=Authorization: Basic "+token)
	}
	cmd.Env = append(env, o.env...)
	if o.stdin != nil {
		cmd.Stdin = bytes.NewReader(o.stdin)
	}
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if o.stdout != nil {
		cmd.Stdout = o.stdout
	}
	err := cmd.Run()
	res := result{stdout: stdout.Bytes(), stderr: strings.TrimSpace(stderr.String())}
	var exit *exec.ExitError
	switch {
	case err == nil:
	case ctx.Err() != nil:
		return res, fmt.Errorf("git %s: %w", args[0], ctx.Err())
	case errors.As(err, &exit):
		res.code = exit.ExitCode()
	default:
		return res, fmt.Errorf("git %s: %w", args[0], err)
	}
	return res, nil
}

func (g *Git) run(ctx context.Context, dir string, args []string, o opts) ([]byte, error) {
	res, err := g.exec(ctx, dir, args, o)
	if err != nil {
		return nil, err
	}
	if res.code != 0 {
		return nil, &Error{Command: args[0], Code: res.code, Stderr: res.stderr}
	}
	return res.stdout, nil
}

// LsRemote lists a remote's branches as a map from branch name to commit
// SHA, without fetching any objects. It leaves out branches whose names
// start with "-" or aren't valid ref names, and lines without a SHA, which a
// server can add by putting a newline in a ref name.
func (g *Git) LsRemote(ctx context.Context, r Remote) (map[string]string, error) {
	out, err := g.run(ctx, "", []string{"ls-remote", "--end-of-options", r.URL, "refs/heads/*"}, opts{auth: r.Auth})
	if err != nil {
		return nil, err
	}
	heads := map[string]string{}
	for line := range strings.SplitSeq(string(out), "\n") {
		sha, ref, _ := strings.Cut(line, "\t")
		branch, isHead := strings.CutPrefix(ref, "refs/heads/")
		if isHead && objectID(sha) && ValidBranch(branch) {
			heads[branch] = sha
		}
	}
	return heads, nil
}

// objectID reports whether s is a SHA-1 or SHA-256 object ID in hex.
func objectID(s string) bool {
	_, err := hex.DecodeString(s)
	return err == nil && (len(s) == 40 || len(s) == 64)
}

// ValidBranch reports whether refs/heads/name is a valid ref name, as git
// check-ref-format checks, and name doesn't start with "-".
func ValidBranch(name string) bool {
	if name == "" || name[0] == '-' || strings.HasSuffix(name, ".") ||
		strings.Contains(name, "..") || strings.Contains(name, "@{") ||
		strings.ContainsAny(name, " ~^:?*[\\\x7f") ||
		strings.ContainsFunc(name, func(r rune) bool { return r < ' ' }) {
		return false
	}
	for seg := range strings.SplitSeq(name, "/") {
		if seg == "" || seg[0] == '.' || strings.HasSuffix(seg, ".lock") {
			return false
		}
	}
	return true
}

// Open returns the bare repository at dir, creating it if it doesn't exist.
func (g *Git) Open(ctx context.Context, dir string) (*Repo, error) {
	r := &Repo{git: g, Dir: dir}
	if _, err := os.Stat(filepath.Join(dir, "HEAD")); err == nil {
		return r, nil
	}
	if err := os.MkdirAll(filepath.Dir(dir), 0o755); err != nil {
		return nil, err
	}
	if _, err := g.run(ctx, "", []string{"init", "--quiet", "--bare", dir}, opts{}); err != nil {
		return nil, err
	}
	return r, nil
}

// Repo is a local bare repository.
type Repo struct {
	git *Git
	Dir string
}

func (r *Repo) run(ctx context.Context, args ...string) ([]byte, error) {
	return r.git.run(ctx, r.Dir, args, opts{})
}

func (r *Repo) text(ctx context.Context, args ...string) (string, error) {
	out, err := r.run(ctx, args...)
	return strings.TrimSpace(string(out)), err
}

// Fetch fetches branches from the remote into refs/remotes/origin/.
func (r *Repo) Fetch(ctx context.Context, remote Remote, branches ...string) error {
	args := []string{"fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--end-of-options", remote.URL}
	for _, b := range branches {
		args = append(args, "+refs/heads/"+b+":refs/remotes/origin/"+b)
	}
	_, err := r.git.run(ctx, r.Dir, args, opts{auth: remote.Auth})
	return err
}

// HasCommit reports whether the repository has the commit.
func (r *Repo) HasCommit(ctx context.Context, sha string) (bool, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"cat-file", "-e", "--end-of-options", sha + "^{commit}"}, opts{})
	return err == nil && res.code == 0, err
}

// IsAncestor reports whether ancestor is descendant or one of its
// ancestors.
func (r *Repo) IsAncestor(ctx context.Context, ancestor, descendant string) (bool, error) {
	args := []string{"merge-base", "--is-ancestor", "--end-of-options", ancestor, descendant}
	res, err := r.git.exec(ctx, r.Dir, args, opts{})
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

// MergeBase returns the best common ancestor of two commits, or "" if they
// have none.
func (r *Repo) MergeBase(ctx context.Context, a, b string) (string, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"merge-base", "--end-of-options", a, b}, opts{})
	switch {
	case err != nil:
		return "", err
	case res.code == 0:
		return strings.TrimSpace(string(res.stdout)), nil
	case res.code == 1:
		return "", nil
	}
	return "", &Error{Command: "merge-base", Code: res.code, Stderr: res.stderr}
}

// MergeTree merges two commits without a worktree. It returns the merged
// tree, or the paths that conflict.
func (r *Repo) MergeTree(ctx context.Context, ours, theirs string) (tree string, conflicts []string, err error) {
	args := []string{"merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", "--end-of-options", ours, theirs}
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
	case res.code == 1 && len(fields) > 0:
		return "", fields[1:], nil
	}
	return "", nil, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
}

// Commit is a commit's tree and committer time.
type Commit struct {
	Tree string
	Time int64
}

// Commit returns a commit's tree and committer time.
func (r *Repo) Commit(ctx context.Context, sha string) (Commit, error) {
	out, err := r.text(ctx, "show", "-s", "--format=%T %ct", "--end-of-options", sha)
	if err != nil {
		return Commit{}, err
	}
	tree, ts, ok := strings.Cut(out, " ")
	t, perr := strconv.ParseInt(ts, 10, 64)
	if !ok || perr != nil {
		return Commit{}, fmt.Errorf("git show: unexpected output %q", out)
	}
	return Commit{Tree: tree, Time: t}, nil
}

// CommitTree makes a commit object. The same arguments always make the same
// commit, so two controllers that make the same fix push the same commit.
func (r *Repo) CommitTree(ctx context.Context, tree string, parents []string, message string, id Identity, unix int64) (string, error) {
	args := []string{"commit-tree"}
	for _, p := range parents {
		args = append(args, "-p", p)
	}
	args = append(args, "-F", "-", "--end-of-options", tree)
	date := fmt.Sprintf("@%d +0000", unix)
	env := []string{
		"GIT_AUTHOR_NAME=" + id.Name, "GIT_AUTHOR_EMAIL=" + id.Email, "GIT_AUTHOR_DATE=" + date,
		"GIT_COMMITTER_NAME=" + id.Name, "GIT_COMMITTER_EMAIL=" + id.Email, "GIT_COMMITTER_DATE=" + date,
	}
	out, err := r.git.run(ctx, r.Dir, args, opts{stdin: []byte(message), env: env})
	return strings.TrimSpace(string(out)), err
}

// RefUpdate is one ref update in a push.
type RefUpdate struct {
	// Ref is the full ref name on the remote, such as refs/heads/main.
	Ref string
	// New is the commit to set the ref to, or "" to delete the ref.
	New string
	// Old is the commit that the ref must point to for the update to
	// happen, or "" if the ref must not exist.
	Old string
}

// ErrRejected is wrapped by errors from Push when the remote refused an
// update, usually because a ref no longer pointed at the expected commit.
var ErrRejected = errors.New("push rejected")

// PushError is the error from Push when git or the remote rejects the
// updates. It wraps ErrRejected.
type PushError struct {
	// Rejected maps each rejected ref to git's summary of why, such as
	// "[rejected] (stale info)" for a lease that doesn't hold, or
	// "[remote rejected] (deletion prohibited)".
	Rejected map[string]string
}

func (e *PushError) Error() string {
	var refs []string
	for _, ref := range slices.Sorted(maps.Keys(e.Rejected)) {
		refs = append(refs, ref+" "+e.Rejected[ref])
	}
	return fmt.Sprintf("%v: %s", ErrRejected, strings.Join(refs, "; "))
}

func (e *PushError) Unwrap() error { return ErrRejected }

// Refused reports whether the remote refused to update ref for a reason of
// its own, such as a rule against deleting the branch or replacing its
// commits, and not because another update in an atomic push failed.
func (e *PushError) Refused(ref string) bool {
	reason, ok := strings.CutPrefix(e.Rejected[ref], "[remote rejected]")
	return ok && !strings.Contains(reason, "atomic")
}

// Push updates refs on the remote atomically. Each update carries a lease,
// so the push fails with a PushError unless every ref still points at the
// commit that the update expects.
func (r *Repo) Push(ctx context.Context, remote Remote, updates ...RefUpdate) error {
	args := []string{"push", "--porcelain", "--atomic"}
	for _, u := range updates {
		args = append(args, "--force-with-lease="+u.Ref+":"+u.Old)
	}
	args = append(args, "--end-of-options", remote.URL)
	for _, u := range updates {
		args = append(args, u.New+":"+u.Ref)
	}
	res, err := r.git.exec(ctx, r.Dir, args, opts{auth: remote.Auth})
	if err != nil {
		return err
	}
	// A rejected update's line is "!", "source:ref", and git's summary,
	// separated by tabs. A source is a SHA, empty, or "(delete)", so the
	// ref starts after the first colon.
	rejected := map[string]string{}
	for line := range strings.SplitSeq(string(res.stdout), "\n") {
		if rest, ok := strings.CutPrefix(line, "!\t"); ok {
			update, summary, _ := strings.Cut(rest, "\t")
			_, ref, _ := strings.Cut(update, ":")
			rejected[ref] = summary
		}
	}
	if len(rejected) > 0 {
		return &PushError{Rejected: rejected}
	}
	if res.code != 0 {
		return &Error{Command: "push", Code: res.code, Stderr: res.stderr}
	}
	return nil
}

// CountFixerCommits counts the commits in head but not in base that carry
// the fixer trailer. With base "", it counts every commit in head.
func (r *Repo) CountFixerCommits(ctx context.Context, base, head string) (int, error) {
	return r.CountCommits(ctx, base, head, FixerTrailer)
}

// CountCommits counts the commits in head but not in base that carry any
// of the trailers, or every such commit if there are no trailers. With
// base "", it counts commits in all of head's history.
func (r *Repo) CountCommits(ctx context.Context, base, head string, trailers ...string) (int, error) {
	args := []string{"rev-list", "--count"}
	for _, t := range trailers {
		args = append(args, "--grep=^"+t+":")
	}
	args = append(args, "--end-of-options", head)
	if base != "" {
		args = append(args, "^"+base)
	}
	out, err := r.text(ctx, args...)
	if err != nil {
		return 0, err
	}
	return strconv.Atoi(out)
}

// ListedCommit is one commit that ListCommits lists.
type ListedCommit struct {
	SHA string
	// Committer is the committer's name and email as the commit has them,
	// which match Identity.Written of the identity that made the commit.
	Committer Identity
	// Trailers are the trailers at the end of the message, as git parses
	// them, such as "Git-K8s-Fixer: gofmt".
	Trailers []string
}

// ListCommits lists the commits in head but not in base. It lists at most
// limit commits, so a caller that asks for one more than it wants can tell
// when there are too many.
func (r *Repo) ListCommits(ctx context.Context, base, head string, limit int) ([]ListedCommit, error) {
	out, err := r.run(ctx, "log", "-z", "--no-use-mailmap", "--max-count="+strconv.Itoa(limit),
		"--format=%H%x00%cn%x00%ce%x00%(trailers:only,unfold)", "--end-of-options", head, "^"+base)
	if err != nil {
		return nil, err
	}
	// Each commit is 4 fields, each followed by a NUL. git stops printing a
	// name or a trailer at a NUL inside it, so a commit can't add fields.
	const n = 4
	fields := strings.Split(string(out), "\x00")
	if len(fields)%n != 1 {
		return nil, fmt.Errorf("git log: unexpected output")
	}
	var commits []ListedCommit
	for f := fields; len(f) > 1; f = f[n:] {
		commits = append(commits, ListedCommit{
			SHA:       f[0],
			Committer: Identity{Name: f[1], Email: f[2]},
			Trailers:  strings.FieldsFunc(f[3], func(r rune) bool { return r == '\n' }),
		})
	}
	return commits, nil
}

// FileStat is one file's line counts from git diff --numstat. Binary files
// have counts of -1.
type FileStat struct {
	Path    string
	Added   int
	Removed int
}

// Numstat lists the files that differ between two commits.
func (r *Repo) Numstat(ctx context.Context, base, head string) ([]FileStat, error) {
	out, err := r.run(ctx, "diff", "--numstat", "-z", "--no-renames", "--end-of-options", base, head)
	if err != nil {
		return nil, err
	}
	var stats []FileStat
	for rec := range strings.SplitSeq(string(out), "\x00") {
		parts := strings.SplitN(rec, "\t", 3)
		if len(parts) != 3 {
			continue
		}
		s := FileStat{Path: parts[2], Added: -1, Removed: -1}
		if n, err := strconv.Atoi(parts[0]); err == nil {
			s.Added = n
		}
		if n, err := strconv.Atoi(parts[1]); err == nil {
			s.Removed = n
		}
		stats = append(stats, s)
	}
	return stats, nil
}

// TreeEntry is one file in a tree.
type TreeEntry struct {
	Mode string
	Type string
	SHA  string
	Path string
}

// LsTree lists every file in a commit's tree.
func (r *Repo) LsTree(ctx context.Context, commit string) ([]TreeEntry, error) {
	out, err := r.run(ctx, "ls-tree", "-r", "-z", "--full-tree", "--end-of-options", commit)
	if err != nil {
		return nil, err
	}
	var entries []TreeEntry
	for rec := range strings.SplitSeq(string(out), "\x00") {
		meta, path, ok := strings.Cut(rec, "\t")
		f := strings.Fields(meta)
		if !ok || len(f) != 3 {
			continue
		}
		entries = append(entries, TreeEntry{Mode: f[0], Type: f[1], SHA: f[2], Path: path})
	}
	return entries, nil
}

// ReadBlob returns a blob's contents.
func (r *Repo) ReadBlob(ctx context.Context, sha string) ([]byte, error) {
	return r.run(ctx, "cat-file", "blob", "--end-of-options", sha)
}

// WriteBlob stores a blob and returns its SHA.
func (r *Repo) WriteBlob(ctx context.Context, content []byte) (string, error) {
	out, err := r.git.run(ctx, r.Dir, []string{"hash-object", "-w", "--stdin"}, opts{stdin: content})
	return strings.TrimSpace(string(out)), err
}

var indexes atomic.Int64

// ReplaceFiles returns the SHA of a tree that is tree with files replaced.
// Each entry's Mode, SHA, and Path set one file.
func (r *Repo) ReplaceFiles(ctx context.Context, tree string, files []TreeEntry) (string, error) {
	index := filepath.Join(r.Dir, fmt.Sprintf("git-k8s-%d.index", indexes.Add(1)))
	defer os.Remove(index)
	o := opts{env: []string{"GIT_INDEX_FILE=" + index}}
	if _, err := r.git.run(ctx, r.Dir, []string{"read-tree", "--end-of-options", tree}, o); err != nil {
		return "", err
	}
	var info bytes.Buffer
	for _, f := range files {
		fmt.Fprintf(&info, "%s %s\t%s\x00", f.Mode, f.SHA, f.Path)
	}
	o.stdin = info.Bytes()
	update := []string{"-c", "core.protectHFS=true", "-c", "core.protectNTFS=true", "update-index", "-z", "--index-info"}
	res, err := r.git.exec(ctx, r.Dir, update, o)
	switch {
	case err != nil:
		return "", err
	case res.code != 0:
		return "", &Error{Command: "update-index", Code: res.code, Stderr: res.stderr}
	case res.stderr != "":
		// update-index skips a path that it refuses, such as one that macOS
		// or Windows would read as .git, with only a warning.
		return "", fmt.Errorf("git update-index: %s", res.stderr)
	}
	o.stdin = nil
	out, err := r.git.run(ctx, r.Dir, []string{"write-tree"}, o)
	return strings.TrimSpace(string(out)), err
}

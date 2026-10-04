// Package git runs the git command-line tool.
//
// Controllers keep git objects in local bare repositories and run git
// against them. Only commit SHAs go into Kubernetes objects.
package git

import (
	"bytes"
	"context"
	"encoding/base64"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync/atomic"
	"time"
)

// FixerTrailer is the commit trailer that marks commits pushed by checks.
const FixerTrailer = "Git-K8s-Fixer"

// AgentTrailer is the commit trailer that marks commits with changes that
// an AI agent made.
const AgentTrailer = "Git-K8s-Agent"

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
// SHA, without fetching any objects.
func (g *Git) LsRemote(ctx context.Context, r Remote) (map[string]string, error) {
	out, err := g.run(ctx, "", []string{"ls-remote", r.URL, "refs/heads/*"}, opts{auth: r.Auth})
	if err != nil {
		return nil, err
	}
	heads := map[string]string{}
	for line := range strings.SplitSeq(string(out), "\n") {
		sha, ref, ok := strings.Cut(line, "\t")
		if branch, isHead := strings.CutPrefix(ref, "refs/heads/"); ok && isHead {
			heads[branch] = sha
		}
	}
	return heads, nil
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
	args := []string{"fetch", "--quiet", "--no-tags", "--no-write-fetch-head", remote.URL}
	for _, b := range branches {
		args = append(args, "+refs/heads/"+b+":refs/remotes/origin/"+b)
	}
	_, err := r.git.run(ctx, r.Dir, args, opts{auth: remote.Auth})
	return err
}

// HasCommit reports whether the repository has the commit.
func (r *Repo) HasCommit(ctx context.Context, sha string) (bool, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"cat-file", "-e", sha + "^{commit}"}, opts{})
	return err == nil && res.code == 0, err
}

// IsAncestor reports whether ancestor is descendant or one of its
// ancestors.
func (r *Repo) IsAncestor(ctx context.Context, ancestor, descendant string) (bool, error) {
	args := []string{"merge-base", "--is-ancestor", ancestor, descendant}
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
	res, err := r.git.exec(ctx, r.Dir, []string{"merge-base", a, b}, opts{})
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
	args := []string{"merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", ours, theirs}
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
	out, err := r.text(ctx, "show", "-s", "--format=%T %ct", sha)
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
	args := []string{"commit-tree", tree}
	for _, p := range parents {
		args = append(args, "-p", p)
	}
	args = append(args, "-F", "-")
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

// Push updates refs on the remote atomically. Each update carries a lease,
// so the push fails with ErrRejected unless every ref still points at the
// commit that the update expects.
func (r *Repo) Push(ctx context.Context, remote Remote, updates ...RefUpdate) error {
	args := []string{"push", "--porcelain", "--atomic", remote.URL}
	for _, u := range updates {
		args = append(args, "--force-with-lease="+u.Ref+":"+u.Old)
	}
	for _, u := range updates {
		args = append(args, u.New+":"+u.Ref)
	}
	res, err := r.git.exec(ctx, r.Dir, args, opts{auth: remote.Auth})
	if err != nil {
		return err
	}
	var rejected []string
	for line := range strings.SplitSeq(string(res.stdout), "\n") {
		if rest, ok := strings.CutPrefix(line, "!\t"); ok {
			rejected = append(rejected, rest)
		}
	}
	if len(rejected) > 0 {
		return fmt.Errorf("%w: %s", ErrRejected, strings.Join(rejected, "; "))
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
	args = append(args, head)
	if base != "" {
		args = append(args, "^"+base)
	}
	out, err := r.text(ctx, args...)
	if err != nil {
		return 0, err
	}
	return strconv.Atoi(out)
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
	out, err := r.run(ctx, "diff", "--numstat", "-z", "--no-renames", base, head)
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
	out, err := r.run(ctx, "ls-tree", "-r", "-z", "--full-tree", commit)
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
	return r.run(ctx, "cat-file", "blob", sha)
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
	if _, err := r.git.run(ctx, r.Dir, []string{"read-tree", tree}, o); err != nil {
		return "", err
	}
	var info bytes.Buffer
	for _, f := range files {
		fmt.Fprintf(&info, "%s %s\t%s\x00", f.Mode, f.SHA, f.Path)
	}
	o.stdin = info.Bytes()
	if _, err := r.git.run(ctx, r.Dir, []string{"update-index", "-z", "--index-info"}, o); err != nil {
		return "", err
	}
	o.stdin = nil
	out, err := r.git.run(ctx, r.Dir, []string{"write-tree"}, o)
	return strings.TrimSpace(string(out)), err
}

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
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
	"time"
)

// FixerTrailer is the commit trailer that marks commits pushed by checks.
const FixerTrailer = "Git-K8s-Fixer"

// AllowProtocol is the GIT_ALLOW_PROTOCOL setting that git-k8s runs git
// with. It allows only the transports that a GitRepository's URL can name.
// It leaves out file, which also covers plain paths, so git can't read a
// local repository such as another GitRepository's cache.
const AllowProtocol = "http:https:git:ssh"

// Auth is a username and password for HTTP basic authentication, or a
// bearer token.
type Auth struct {
	Username string
	Password string
	// Token, when set, is sent as a bearer token instead of the username
	// and password.
	Token string
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

// stopDelay is how long a command has to exit after its context ends and
// it gets SIGTERM, before it gets SIGKILL. git removes its lock files when
// it gets SIGTERM, but not when it gets SIGKILL.
const stopDelay = 10 * time.Second

// MaxDuration returns the longest that a command that g runs can take. By
// then, the command has exited or been killed.
func (g *Git) MaxDuration() time.Duration { return g.timeout() + stopDelay }

func (g *Git) timeout() time.Duration {
	if g.Timeout == 0 {
		return 5 * time.Minute
	}
	return g.Timeout
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
	// in and out, when set, stream the command's standard input and
	// output instead of stdin and the result's stdout.
	in  io.Reader
	out io.Writer
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
	ctx, cancel := context.WithTimeout(ctx, g.timeout())
	defer cancel()

	if dir != "" {
		args = append([]string{"-C", dir}, args...)
	}
	cmd := exec.CommandContext(ctx, bin, args...)
	cmd.Cancel = func() error { return cmd.Process.Signal(syscall.SIGTERM) }
	cmd.WaitDelay = stopDelay
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
		header := "Authorization: Bearer " + o.auth.Token
		if o.auth.Token == "" {
			header = "Authorization: Basic " + base64.StdEncoding.EncodeToString([]byte(o.auth.Username+":"+o.auth.Password))
		}
		env = append(env, "GIT_CONFIG_COUNT=1", "GIT_CONFIG_KEY_0=http.extraHeader", "GIT_CONFIG_VALUE_0="+header)
	}
	cmd.Env = append(env, o.env...)
	switch {
	case o.in != nil:
		cmd.Stdin = o.in
	case o.stdin != nil:
		cmd.Stdin = bytes.NewReader(o.stdin)
	}
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if o.out != nil {
		cmd.Stdout = o.out
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

// Advertise writes the refs of the repository at dir for the info/refs
// response to a smart HTTP request. Service is upload-pack or receive-pack,
// and protocol is the request's Git-Protocol header.
func (g *Git) Advertise(ctx context.Context, service, dir, protocol string, w io.Writer) error {
	return g.service(ctx, service, dir, protocol, nil, w, "--advertise-refs")
}

// Serve runs upload-pack or receive-pack on the repository at dir with the
// body of a smart HTTP request, and writes the response to w.
func (g *Git) Serve(ctx context.Context, service, dir, protocol string, r io.Reader, w io.Writer) error {
	return g.service(ctx, service, dir, protocol, r, w)
}

func (g *Git) service(ctx context.Context, service, dir, protocol string, r io.Reader, w io.Writer, extra ...string) error {
	if service != "upload-pack" && service != "receive-pack" {
		return fmt.Errorf("git: no service %q", service)
	}
	args := append(append([]string{service, "--stateless-rpc"}, extra...), "--end-of-options", dir)
	_, err := g.run(ctx, "", args, opts{in: r, out: w, env: []string{"GIT_PROTOCOL=" + protocol}})
	return err
}

// Repo is a local bare repository.
type Repo struct {
	git *Git
	Dir string
}

// Config returns the value of a key in the repository's configuration, or
// false if the key isn't set.
func (r *Repo) Config(ctx context.Context, key string) (string, bool, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"config", "--get", "--end-of-options", key}, opts{})
	switch {
	case err != nil:
		return "", false, err
	case res.code == 0:
		return strings.TrimSpace(string(res.stdout)), true, nil
	case res.code == 1:
		return "", false, nil
	}
	return "", false, &Error{Command: "config", Code: res.code, Stderr: res.stderr}
}

// SetConfig sets a key in the repository's configuration.
func (r *Repo) SetConfig(ctx context.Context, key, value string) error {
	_, err := r.run(ctx, "config", "--end-of-options", key, value)
	return err
}

// Refs lists the refs that match patterns, such as refs/heads, as a map
// from ref name to commit SHA. A pattern matches a ref with that name and
// the refs under it.
func (r *Repo) Refs(ctx context.Context, patterns ...string) (map[string]string, error) {
	out, err := r.run(ctx, append([]string{"for-each-ref", "--format=%(objectname) %(refname)", "--end-of-options"}, patterns...)...)
	if err != nil {
		return nil, err
	}
	refs := map[string]string{}
	for line := range strings.SplitSeq(string(out), "\n") {
		if sha, ref, ok := strings.Cut(line, " "); ok {
			refs[ref] = sha
		}
	}
	return refs, nil
}

// UpdateRefs changes refs in the repository in one transaction. Each
// update carries a lease: either every ref points at the commit that its
// update expects and they all change, or nothing changes and the error
// wraps ErrRejected. Other errors, such as a lock file that a killed git
// left, don't wrap ErrRejected, because they last until someone fixes
// them.
func (r *Repo) UpdateRefs(ctx context.Context, updates ...RefUpdate) error {
	var in strings.Builder
	for _, u := range updates {
		// update-ref reads one command per line, its fields separated by
		// spaces.
		for _, s := range []string{u.Ref, u.New, u.Old} {
			if strings.ContainsFunc(s, func(c rune) bool { return c <= ' ' || c == 0x7f }) {
				return fmt.Errorf("git: %q has a space or a control character", s)
			}
		}
		switch {
		case u.New != "" && u.Old != "":
			fmt.Fprintf(&in, "update %s %s %s\n", u.Ref, u.New, u.Old)
		case u.New != "":
			fmt.Fprintf(&in, "create %s %s\n", u.Ref, u.New)
		case u.Old != "":
			fmt.Fprintf(&in, "delete %s %s\n", u.Ref, u.Old)
		default:
			fmt.Fprintf(&in, "verify %s\n", u.Ref)
		}
	}
	res, err := r.git.exec(ctx, r.Dir, []string{"update-ref", "--stdin"}, opts{stdin: []byte(in.String())})
	switch {
	case err != nil:
		return err
	case res.code == 0:
		return nil
	case leaseFailed.MatchString(res.stderr):
		return fmt.Errorf("%w: %s", ErrRejected, res.stderr)
	}
	return &Error{Command: "update-ref", Code: res.code, Stderr: res.stderr}
}

// leaseFailed matches update-ref's message when a ref doesn't point at the
// commit that its update expects, or exists when the update expects it not
// to. A ref name can't hold a colon.
var leaseFailed = regexp.MustCompile(`cannot lock ref '[^:]*': (is at [0-9a-f]+ but expected [0-9a-f]+|reference already exists|reference is missing but expected [0-9a-f]+|unable to resolve reference)`)

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

// FetchPrune fetches the refs that refspec maps from the remote, such as
// +refs/heads/*:refs/copy/*, and deletes the local refs that it maps to
// that the remote no longer has.
func (r *Repo) FetchPrune(ctx context.Context, remote Remote, refspec string) error {
	args := []string{"fetch", "--quiet", "--no-tags", "--prune", "--no-write-fetch-head", "--end-of-options", remote.URL, refspec}
	_, err := r.git.run(ctx, r.Dir, args, opts{auth: remote.Auth})
	return err
}

// Maintain runs git's automatic maintenance, such as packing loose
// objects, if the repository needs it. It runs in the foreground, under
// the command's timeout. Before git 2.47, the gc that maintenance starts
// goes to the background unless gc.autoDetach is false.
func (r *Repo) Maintain(ctx context.Context) error {
	_, err := r.git.run(ctx, r.Dir, []string{"maintenance", "run", "--auto", "--quiet"}, opts{
		env: []string{"GIT_CONFIG_COUNT=1", "GIT_CONFIG_KEY_0=gc.autoDetach", "GIT_CONFIG_VALUE_0=false"},
	})
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

// MergeBases returns every best common ancestor of two commits: the common
// ancestors that aren't ancestors of another common ancestor. It returns
// none if the commits have no common ancestor.
func (r *Repo) MergeBases(ctx context.Context, a, b string) ([]string, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"merge-base", "--all", "--end-of-options", a, b}, opts{})
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

// KeepsChanges reports whether head's files have every change from base's
// files to other's: merging other into head, with base as the merge base,
// is clean and leaves head's tree as it is. base needn't be an ancestor of
// either commit, so if other removed lines that base has, head must not
// have them either. It compares only files, so a reworded commit, or a
// commit and its revert, changes nothing that it can see.
//
// A change that head made right next to one of other's changes, or on
// the same lines, conflicts, so KeepsChanges can report false for a head
// that does have the change. It never reports true for one that doesn't.
func (r *Repo) KeepsChanges(ctx context.Context, head, other, base string) (bool, error) {
	args := []string{"merge-tree", "--write-tree", "--no-messages", "--merge-base=" + base, "--end-of-options", head, other}
	res, err := r.git.exec(ctx, r.Dir, args, opts{})
	switch {
	case err != nil:
		return false, err
	case res.code == 1:
		return false, nil
	case res.code != 0:
		return false, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
	}
	tree, _, _ := strings.Cut(string(res.stdout), "\n")
	headTree, err := r.text(ctx, "rev-parse", "--verify", "--end-of-options", head+"^{tree}")
	return err == nil && tree == headTree, err
}

// Replays reports whether head has a replay of each commit that's in other
// but not in head or base: a commit in head but not in other that removes
// and adds the same lines in the same files. Each commit in head replays at
// most one commit. A merge commit, and a commit that changes no file, have
// no replay.
//
// Unlike git cherry, Replays ignores the unchanged lines around each
// change, so a commit replayed onto a base that changed nearby lines still
// matches. It also ignores where in a file each change is, and whitespace,
// so a commit that changes "foo" to "bar" on line 10 replays one that
// makes the same change on line 50. Use it with KeepsChanges, which
// compares where the changes are but not the commits that made them.
func (r *Repo) Replays(ctx context.Context, head, other, base string) (bool, error) {
	out, err := r.run(ctx, "rev-list", "--parents", "--end-of-options", other, "^"+head, "^"+base)
	if err != nil {
		return false, err
	}
	var commits []string
	for line := range strings.Lines(string(out)) {
		f := strings.Fields(line)
		if len(f) > 2 {
			return false, nil
		}
		commits = append(commits, f[0])
	}
	if len(commits) == 0 {
		return true, nil
	}
	need, err := r.patchIDs(ctx, commits)
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
	out, err = r.run(ctx, "rev-list", "--no-merges", "--end-of-options", head, "^"+other)
	if err != nil {
		return false, err
	}
	// rev-list lists the newest commits first, and replays are usually the
	// newest, so hash head's commits in growing batches and stop once each
	// commit has a replay. head can hold thousands of commits that other
	// doesn't, such as a main branch that it was rebased onto.
	have := strings.Fields(string(out))
	for n := 64; len(have) > 0 && len(missing) > 0; n *= 2 {
		batch := have[:min(n, len(have))]
		have = have[len(batch):]
		ids, err := r.patchIDs(ctx, batch)
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

// patchIDs maps each commit to the patch ID of its change from its parent,
// computed from a diff without context lines, or to "" if the commit
// changes no file. patch-id identifies a binary file's change by the blobs'
// full names, which --full-index prints, so the diff needn't carry the
// files' contents.
func (r *Repo) patchIDs(ctx context.Context, commits []string) (map[string]string, error) {
	ids := map[string]string{}
	if len(commits) == 0 {
		return ids, nil
	}
	diffs, err := r.git.run(ctx, r.Dir, []string{"diff-tree", "--stdin", "--root", "-p", "-U0", "--full-index"},
		opts{stdin: []byte(strings.Join(commits, "\n") + "\n")})
	if err != nil {
		return nil, err
	}
	out, err := r.git.run(ctx, r.Dir, []string{"patch-id", "--stable"}, opts{stdin: diffs})
	if err != nil {
		return nil, err
	}
	for _, c := range commits {
		ids[c] = ""
	}
	for line := range strings.Lines(string(out)) {
		if id, commit, ok := strings.Cut(strings.TrimSpace(line), " "); ok {
			ids[commit] = id
		}
	}
	return ids, nil
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

// ErrRejected is wrapped by errors from Push and UpdateRefs when an update
// was refused, usually because a ref no longer pointed at the expected
// commit.
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

// PushEach pushes updates to the remote, each with its own lease, so that a
// rejected update doesn't stop the others. It returns why the remote
// rejected each update that it rejected, by ref. An error means that the
// push didn't happen.
func (r *Repo) PushEach(ctx context.Context, remote Remote, updates ...RefUpdate) (map[string]string, error) {
	if len(updates) == 0 {
		return nil, nil
	}
	args := []string{"push", "--porcelain"}
	for _, u := range updates {
		args = append(args, "--force-with-lease="+u.Ref+":"+u.Old)
	}
	args = append(args, "--end-of-options", remote.URL)
	for _, u := range updates {
		args = append(args, u.New+":"+u.Ref)
	}
	res, err := r.git.exec(ctx, r.Dir, args, opts{auth: remote.Auth})
	if err != nil {
		return nil, err
	}
	rejected := map[string]string{}
	reported := false
	for line := range strings.SplitSeq(string(res.stdout), "\n") {
		// Each ref's line is FLAG, FROM:TO, and a summary, separated by tabs.
		f := strings.SplitN(line, "\t", 3)
		if len(f) != 3 || len(f[0]) != 1 {
			continue
		}
		reported = true
		if f[0] == "!" {
			rejected[f[1][strings.LastIndex(f[1], ":")+1:]] = f[2]
		}
	}
	if !reported && res.code != 0 {
		return nil, &Error{Command: "push", Code: res.code, Stderr: res.stderr}
	}
	return rejected, nil
}

// CountFixerCommits counts the commits in head but not in base that carry
// the fixer trailer. With base "", it counts every commit in head.
func (r *Repo) CountFixerCommits(ctx context.Context, base, head string) (int, error) {
	args := []string{"rev-list", "--count", "--grep=^" + FixerTrailer + ":", head}
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

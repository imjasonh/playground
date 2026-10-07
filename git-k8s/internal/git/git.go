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
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
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
// local repository such as another GitRepository's cache. Commands that
// read only local objects need it too, because a repository with a
// promisor remote fetches the objects that it lacks.
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

	// Options such as --attr-source, and -c with its value, can come before
	// git's command.
	command := args[0]
	for i := 0; i < len(args); i++ {
		if args[i] == "-c" {
			i++
		} else if !strings.HasPrefix(args[i], "-") {
			command = args[i]
			break
		}
	}
	if dir != "" {
		args = append([]string{"-C", dir}, args...)
	}
	// Keep the automatic maintenance that fetch starts in the foreground.
	// Detached, it outlives the command. It can still be writing to a cache
	// while the cache is removed, and where PID 1 is a Go program, which
	// never waits for it, each fetch leaves a zombie. Git uses gc.autoDetach
	// when maintenance.autoDetach isn't set.
	cmd := exec.CommandContext(ctx, bin, append([]string{"-c", "gc.autoDetach=false"}, args...)...)
	// git runs in its own process group, and the group gets SIGTERM, so
	// the commands that git started stop too. Otherwise the repack that
	// maintenance starts outlives it, holding git's output open until
	// stopDelay passes and then running beside the next maintenance.
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	cmd.Cancel = func() error {
		if err := syscall.Kill(-cmd.Process.Pid, syscall.SIGTERM); !errors.Is(err, syscall.ESRCH) {
			return err
		}
		return os.ErrProcessDone
	}
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
		return res, fmt.Errorf("git %s: %w", command, ctx.Err())
	case errors.As(err, &exit):
		res.code = exit.ExitCode()
	default:
		return res, fmt.Errorf("git %s: %w", command, err)
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
	args := []string{"fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--end-of-options", remote.URL}
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
// the command's timeout, because Git sets gc.autoDetach to false for
// every command.
func (r *Repo) Maintain(ctx context.Context) error {
	_, err := r.run(ctx, "maintenance", "run", "--auto", "--quiet")
	return err
}

// Fetched returns the commit that the last Fetch of a branch found.
func (r *Repo) Fetched(ctx context.Context, branch string) (string, error) {
	return r.text(ctx, "rev-parse", "--verify", "--end-of-options", "refs/remotes/origin/"+branch+"^{commit}")
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
// tree, or the paths that conflict. Attributes from the commits'
// .gitattributes files don't apply, so a branch can't choose how its own
// conflicts merge.
func (r *Repo) MergeTree(ctx context.Context, ours, theirs string) (tree string, conflicts []string, err error) {
	noAttrs, err := r.noAttributes(ctx)
	if err != nil {
		return "", nil, err
	}
	args := []string{noAttrs, "merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", "--end-of-options", ours, theirs}
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

// CommitTree is WriteCommit with id as the author and committer, at the
// time unix in UTC. Two controllers that make the same fix push the same
// commit, unless an ECDSA key signs it, as WriteCommit describes.
func (r *Repo) CommitTree(ctx context.Context, tree string, parents []string, message string, id Identity, unix int64, key *SigningKey) (string, error) {
	sig := Signature{Name: id.Name, Email: id.Email, Date: fmt.Sprintf("%d +0000", unix)}
	return r.WriteCommit(ctx, NewCommit{Tree: tree, Parents: parents, Author: sig, Committer: sig, Message: message}, key)
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
// is refused, because a ref no longer points at the expected commit or, for
// Push, because the remote declines it, as a forge does for a push that
// breaks a branch protection rule. Push's error ends with the remote's
// messages, which usually say why.
var ErrRejected = errors.New("push rejected")

// PushError is the error from Push when git or the remote rejects the
// updates. It wraps ErrRejected.
type PushError struct {
	// Rejected maps each rejected ref to git's summary of why, such as
	// "[rejected] (stale info)" for a lease that doesn't hold, or
	// "[remote rejected] (deletion prohibited)".
	Rejected map[string]string
	// Remote holds the messages that the remote sent, such as the reasons
	// that a forge gives for refusing a push.
	Remote []string
}

func (e *PushError) Error() string {
	var refs []string
	for _, ref := range slices.Sorted(maps.Keys(e.Rejected)) {
		refs = append(refs, ref+" "+e.Rejected[ref])
	}
	return fmt.Sprintf("%v: %s", ErrRejected, e.withRemote(refs))
}

func (e *PushError) Unwrap() error { return ErrRejected }

// Reason returns git's summary of why ref's update was rejected, followed
// by the remote's messages. A forge's summary only says that a rule refused
// the push, and its messages name the rule.
func (e *PushError) Reason(ref string) string {
	return e.withRemote([]string{e.Rejected[ref]})
}

func (e *PushError) withRemote(parts []string) string {
	for _, msg := range e.Remote {
		parts = append(parts, "remote: "+msg)
	}
	return strings.Join(parts, "; ")
}

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
		return &PushError{Rejected: rejected, Remote: remoteMessages(res.stderr)}
	}
	if res.code != 0 {
		return &Error{Command: "push", Code: res.code, Stderr: res.stderr}
	}
	return nil
}

// remoteMessages returns the messages that the remote sent, from the lines
// of git's stderr that start with "remote:".
func remoteMessages(stderr string) []string {
	var msgs []string
	for line := range strings.SplitSeq(stderr, "\n") {
		if msg, ok := strings.CutPrefix(line, "remote:"); ok && strings.TrimSpace(msg) != "" {
			msgs = append(msgs, strings.TrimSpace(msg))
		}
	}
	return msgs
}

// PushEach pushes updates to the remote, each with its own lease, so that a
// rejected update doesn't stop the others. It returns why the remote
// rejected each update that it rejected, by ref, as PushError's Reason
// does: git's summary followed by the remote's messages. An error means
// that the push didn't happen.
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
	e := &PushError{Rejected: rejected, Remote: remoteMessages(res.stderr)}
	reasons := make(map[string]string, len(rejected))
	for ref := range rejected {
		reasons[ref] = e.Reason(ref)
	}
	return reasons, nil
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

// OnlyFixerCommits reports whether head descends from base, and every
// commit after base on head's first-parent history carries the fixer
// trailer, so that checks made every change since base. A merge of the
// parent into the branch has the branch as its first parent, so the parent's
// own commits don't count.
func (r *Repo) OnlyFixerCommits(ctx context.Context, base, head string) (bool, error) {
	if ok, err := r.IsAncestor(ctx, base, head); err != nil || !ok {
		return false, err
	}
	out, err := r.text(ctx, "rev-list", "--first-parent", "--invert-grep", "--grep=^"+FixerTrailer+":", "--end-of-options", head, "^"+base)
	return err == nil && out == "", err
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

// Numstat lists the files that differ between two commits. If the list
// takes more than MaxChangeBytes, the error wraps ErrTooBig.
func (r *Repo) Numstat(ctx context.Context, base, head string) ([]FileStat, error) {
	out, err := r.limited(ctx, MaxChangeBytes, "diff", "--numstat", "-z", "--no-renames", "--end-of-options", base, head)
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

// MaxTreeBytes is the most output that LsTree reads from git, enough for
// about 150,000 files. A pack of a few hundred bytes can hold a tree that
// lists millions of files, because a tree can list one subtree many times.
const MaxTreeBytes = 16 << 20

// MaxBlobBytes is the largest blob that ReadBlob reads.
const MaxBlobBytes = 8 << 20

// ErrTooBig is the error, wrapped, from a reader such as ReadBlob when
// git prints more than the reader's limit.
var ErrTooBig = errors.New("more output than the limit")

// LsTree lists every file in a commit's tree. If the list takes more than
// MaxTreeBytes, the error wraps ErrTooBig.
func (r *Repo) LsTree(ctx context.Context, commit string) ([]TreeEntry, error) {
	out, err := r.limited(ctx, MaxTreeBytes, "ls-tree", "-r", "-z", "--full-tree", "--end-of-options", commit)
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

// BlobSizes returns the size in bytes of each blob in shas, so that a
// caller can skip a blob that's larger than MaxBlobBytes without reading
// it. It fails if an object is missing or isn't a blob.
func (r *Repo) BlobSizes(ctx context.Context, shas []string) (map[string]int64, error) {
	sizes := map[string]int64{}
	var names []string
	var in strings.Builder
	for _, sha := range shas {
		if !objectID(sha) {
			return nil, fmt.Errorf("git cat-file: %q isn't an object name", sha)
		}
		if _, ok := sizes[sha]; !ok {
			sizes[sha] = 0
			names = append(names, sha)
			in.WriteString(sha + "\n")
		}
	}
	if len(names) == 0 {
		return sizes, nil
	}
	// git prints a line for each name, less than twice as long as the
	// name, so the output needs no limit.
	out, err := r.git.run(ctx, r.Dir, []string{"cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)"}, opts{stdin: []byte(in.String())})
	if err != nil {
		return nil, err
	}
	lines := strings.Split(strings.TrimSuffix(string(out), "\n"), "\n")
	if len(lines) != len(names) {
		return nil, fmt.Errorf("git cat-file: printed %d lines for %d objects", len(lines), len(names))
	}
	for i, line := range lines {
		f := strings.Fields(line)
		if len(f) != 3 || f[0] != names[i] || f[1] != "blob" {
			return nil, fmt.Errorf("git cat-file: %s isn't a blob: %q", names[i], line)
		}
		n, err := strconv.ParseInt(f[2], 10, 64)
		if err != nil {
			return nil, fmt.Errorf("git cat-file: %s has the size %q", names[i], f[2])
		}
		sizes[names[i]] = n
	}
	return sizes, nil
}

// ReadBlob returns a blob's contents. If the blob is larger than
// MaxBlobBytes, the error wraps ErrTooBig.
func (r *Repo) ReadBlob(ctx context.Context, sha string) ([]byte, error) {
	return r.limited(ctx, MaxBlobBytes, "cat-file", "blob", "--end-of-options", sha)
}

// limited runs git in the repository like run, but reads at most limit
// bytes of its output. If git prints more, the error wraps ErrTooBig.
func (r *Repo) limited(ctx context.Context, limit int, args ...string) ([]byte, error) {
	out := &limitedWriter{n: limit}
	_, err := r.git.run(ctx, r.Dir, args, opts{out: out})
	if out.full {
		// git dies when the write fails, so err doesn't say why.
		return nil, fmt.Errorf("git %s: %w of %d MiB", args[0], ErrTooBig, limit>>20)
	}
	if err != nil {
		return nil, err
	}
	return out.b, nil
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

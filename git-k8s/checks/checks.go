// Package checks runs check controllers.
//
// A check controller reads GitBranch objects through its own view type,
// which declares the branch's spec and only the check's entry in
// status.checks:
//
//	type Branch struct {
//		kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
//		Spec        gitk8s.GitBranchSpec `json:"spec"`
//		Status      struct {
//			Checks struct {
//				Result *gitk8s.CheckResult `json:"gofmt,omitempty"`
//			} `json:"checks,omitzero"`
//		} `json:"status,omitzero"`
//	}
//
//	func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
//		return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
//	}
//
// The controller reconciles a view of GitBranch without a status, so it
// can't write status. It reads the check's last result through the check's
// view, and sends each new result to the core program with a token for the
// check's service account. The core program writes the result to the
// check's entry and no other. Other checks' entries never pass through the
// controller, and because its caches don't decode them, their changes don't
// make it reconcile.
package checks

import (
	"cmp"
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"maps"
	"net/http"
	"os"
	"slices"
	"strings"
	"sync"
	"time"
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

// View is a check's view of a GitBranch. Parts returns the branch's
// metadata, its spec, and the check's entry in its status.
type View interface {
	Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult)
}

// Check is a check that runs on branches.
type Check struct {
	// Name is the check's name in merge policies and in status.checks.
	Name string
	// UsesParent says the check's result depends on the parent's head as
	// well as the branch's, so the check runs again when the parent moves.
	UsesParent bool
	// SameChange says that the check's result for the branch's head holds
	// for any head that makes the same change on top of its merge base with
	// the parent's head, as git.Repo.SameChange compares them. The
	// framework records the merge base in each Passed or Failed result
	// without a fix. When the head moves, such as to a merge of the parent,
	// a rebase, or a squash, the framework gives the new head the result
	// without running the check if the new head makes the same change. The
	// check doesn't run again when the parent moves, unless the merge base
	// moves too and the change differs. A verdict that depends on more than
	// the change, such as on files at the merge base that the change
	// doesn't touch, sets Verdict.UsesParent. Such a verdict, and one for a
	// head without a single merge base, holds only for the parent's head,
	// as with UsesParent. A check with SameChange sets Remote, because the
	// framework reads the repository, and leaves UsesParent and Always
	// unset.
	SameChange bool
	// FilesOnly says that the check's result for the branch's head also
	// holds for any commit with the same files that builds on the same
	// parent head, because the result doesn't depend on the branch's
	// commits, such as their messages, authors, or signatures. Only such
	// results count for the commits that squash and rebase landings make.
	// For a check without it, the merge controller pushes those commits to
	// the branch, and the check runs on them before they land.
	FilesOnly bool
	// Always runs the check on every reconcile, instead of only when the
	// heads change. Use it for checks that read more of the GitBranch
	// object than its heads, such as an annotation.
	Always bool
	// Stale, when set, reports whether a final result for the branch's
	// current heads needs the check to run again anyway, for a check whose
	// result depends on more than the heads. It can read objects with
	// kube.Get, and a change to one of them calls it again.
	Stale func(ctx context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool
	// Remote returns a repository's URL and credentials, given the core
	// program's URL from Config.CoreURL. A check that calls Input.Repo or
	// returns a Fix sets it to mirror.Remote, which reaches the
	// repository's copy on the core program's mirror. A check that leaves
	// it nil doesn't link that package, so its program gets no token for
	// the mirror.
	Remote func(ctx context.Context, coreURL string, repo *gitk8s.Repository) (git.Remote, error)
	// SigningKey returns the key that signs a repository's commits, or nil
	// if the repository doesn't name one. A check that calls
	// Input.CommitTree or Input.Replay sets it to signing.Key. A check that
	// leaves it nil doesn't link that package, so its program doesn't read
	// signing keys.
	SigningKey func(context.Context, *gitk8s.Repository) (*git.SigningKey, error)
	// Run examines the branch.
	Run func(ctx context.Context, in *Input) (Verdict, error)
}

// Verdict is the outcome of running a check. The framework shortens the
// message, output values, and note values to fit the core program's limits,
// and reports an Error result instead of a verdict that the core program
// doesn't accept, such as one with more than gitk8s.MaxOutputs outputs.
type Verdict struct {
	// State is Passed, Failed, or Running.
	State   string
	Message string
	// Outputs are values that merge gates read, such as a risk level.
	Outputs map[string]string
	// Notes are other values that the check records, such as what its next
	// run needs or what an agent's run used, and merge gates don't see them.
	// They replace the previous result's notes, so a check that keeps a
	// value copies it from Input.Previous. When the framework reports Error
	// instead of the verdict, the result keeps the verdict's notes if the
	// core program accepts them, and otherwise the previous result's notes,
	// as it does when Run returns an error.
	Notes map[string]string
	// Pod names a Pod that does the check's work, such as one that runs
	// tests. While the result is Running, the mirror lets that Pod fetch
	// the repository.
	Pod string
	// Fix, when set, is a commit that fixes what the check found, such as a
	// commit on top of the branch's head. The framework moves the branch to
	// it with a lease on the head, even if it doesn't contain the head, when
	// the check's policy allows and the branch has automated commits left,
	// and reports Fixed, with the commit in the result's fix; otherwise it
	// reports Failed. It reports Error instead, and doesn't move the branch,
	// if the core program wouldn't accept the Fixed result.
	Fix string
	// UsesParent says that this verdict depends on the parent's head, as
	// Check.UsesParent says of every verdict, so the check runs again when
	// the parent moves.
	UsesParent bool
	// MergeBase, for a check without SameChange, is the merge base of the
	// branch's head and the parent's head that the verdict holds for, such
	// as one that a check that compares changes found. The result records
	// it with the scope Change, and the merge controller lands the branch
	// only when it's the parent's head. When the parent moves, the check
	// runs again unless the head's merge base with it stays the same. A
	// verdict that depends on the parent's head holds only for that head,
	// so its result has the scope Parent and no merge base.
	MergeBase string
}

// ErrUnknownCommit is what Input's methods return, wrapped, for a commit
// that the repository doesn't have, such as one that no branch has pointed
// to for long enough that git removed it.
var ErrUnknownCommit = errors.New("the repository doesn't have the commit")

// Pass returns a passing verdict.
func Pass(format string, args ...any) Verdict {
	return Verdict{State: gitk8s.Passed, Message: fmt.Sprintf(format, args...)}
}

// Fail returns a failing verdict.
func Fail(format string, args ...any) Verdict {
	return Verdict{State: gitk8s.Failed, Message: fmt.Sprintf(format, args...)}
}

// Config holds what check controllers need to work with git and to reach
// the core program.
type Config struct {
	Git      git.Git
	CacheDir string
	Identity git.Identity
	// CoreURL is the core program's base URL. Checks fetch from and push
	// to its mirror, and send results to its results endpoint.
	CoreURL string
}

// AddFlags registers flags that set c: -git, -cache-dir, -identity-name,
// -identity-email, and -core-url.
func (c *Config) AddFlags(fs *flag.FlagSet) {
	fs.StringVar(&c.Git.Bin, "git", "git", "git executable")
	fs.StringVar(&c.CacheDir, "cache-dir", gitk8s.DefaultCacheDir, "writable directory for local copies of repositories")
	fs.StringVar(&c.Identity.Name, "identity-name", "git-k8s", "author and committer name of commits that the controller pushes")
	fs.StringVar(&c.Identity.Email, "identity-email", "git-k8s@users.noreply.github.com", "author and committer email of commits that the controller pushes")
	fs.StringVar(&c.CoreURL, "core-url", gitk8s.CoreURL, "base URL of the git-k8s core program, which serves the mirror and takes check results")
}

// Main runs a check controller with flags from Config.AddFlags and kube.Main.
func Main[V any, P interface {
	kube.Resource[V]
	View
}](check Check) {
	cfg := &Config{}
	cfg.AddFlags(flag.CommandLine)
	if check.SigningKey != nil {
		RemoveLeftoverSigningKeys()
	}
	kube.Main(For[V, P](check, cfg))
}

// RemoveLeftoverSigningKeys removes the signing keys that an earlier run of
// the program left, when the program runs in a Pod. Main calls it for a
// check that signs commits. A program that signs commits but doesn't call
// Main calls it before it starts its controllers.
func RemoveLeftoverSigningKeys() {
	// A container that's killed while it signs a commit leaves the key in
	// os.TempDir, which generate puts on a volume that outlives the
	// container. Outside a Pod, as in generate or a controller run with
	// -kubeconfig, other processes can be signing in the same directory.
	if os.Getenv("KUBERNETES_SERVICE_HOST") == "" {
		return
	}
	if err := git.RemoveSigningKeys(); err != nil {
		slog.Warn("removing signing keys that an earlier run left", "err", err)
	}
}

// For returns a controller that runs check on every GitBranch whose merge
// policy lists it, and sends each new result to the core program. The
// controller's name is check- followed by the check's name.
func For[V any, P interface {
	kube.Resource[V]
	View
}](check Check, cfg *Config, opts ...kube.Option) kube.Controller {
	return ForReconciler[V, P](check, cfg, NewReconciler[V, P](check, cfg), opts...)
}

// ForReconciler returns a controller like For's that runs r on the check's
// view of each GitBranch instead of NewReconciler's reconciler, for a check
// that does more than run on the branches that its policy lists. r can call
// NewReconciler's reconciler for those branches. The controller sends the
// result that r sets in the view to the core program when it changes.
func ForReconciler[V any, P interface {
	kube.Resource[V]
	View
}](check Check, cfg *Config, r kube.Reconciler[V], opts ...kube.Option) kube.Controller {
	s := &sender{check: check.Name, cfg: cfg, client: &http.Client{Timeout: 30 * time.Second}, delay: 100 * time.Millisecond}
	return kube.For[branch](reconcileFunc(func(ctx context.Context, b *branch) error {
		return runAndSend[V, P](ctx, r, s, b)
	}), append([]kube.Option{kube.Named("check-" + check.Name)}, opts...)...)
}

// NewReconciler returns the reconciler that For runs on the check's view of
// each branch, for tests that call Reconcile directly with a context from
// kube.Fake. It sets the check's result in the view and doesn't send it.
func NewReconciler[V any, P interface {
	kube.Resource[V]
	View
}](check Check, cfg *Config) kube.Reconciler[V] {
	return &reconciler[V, P]{check: check, cfg: cfg}
}

type reconciler[V any, P interface {
	kube.Resource[V]
	View
}] struct {
	check Check
	cfg   *Config
	once  sync.Once
	cache *gitk8s.Cache
	bases memo[commitPair, []string]
	same  memo[changePair, bool]
}

// commitPair names two commits in a repository.
type commitPair struct{ repo, a, b string }

// changePair names two changes in a repository.
type changePair struct {
	repo string
	a, b git.Change
}

// maxMemo is the most entries that a memo holds.
const maxMemo = 4096

// memo remembers values that don't change for the same key, such as the
// merge bases of two commits, across reconciles. It forgets them all
// rather than hold more than maxMemo. It's safe for concurrent use, and a
// nil memo remembers nothing.
type memo[K comparable, V any] struct {
	mu sync.Mutex
	m  map[K]V
}

func (m *memo[K, V]) get(k K) (V, bool) {
	if m == nil {
		var zero V
		return zero, false
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	v, ok := m.m[k]
	return v, ok
}

func (m *memo[K, V]) put(k K, v V) {
	if m == nil {
		return
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.m == nil || len(m.m) >= maxMemo {
		m.m = map[K]V{}
	}
	m.m[k] = v
}

func (r *reconciler[V, P]) Reconcile(ctx context.Context, obj *V) error {
	meta, spec, result := P(obj).Parts()
	policy := spec.Merge.Check(r.check.Name)
	if spec.Parent == "" || policy == nil {
		// The core program removes the results of checks that the policy
		// doesn't list, so there's no result to send.
		*result = nil
		return nil
	}
	if spec.Head == "" || spec.ParentHead == "" {
		return nil
	}
	cur := *result
	stale := func(res *gitk8s.CheckResult) bool {
		return r.check.Stale != nil && r.check.Stale(ctx, meta, spec, res)
	}
	// A result with filesOnly from before the check stopped setting
	// FilesOnly must not count for a squashed or rebased commit, so the
	// check runs again. A result without filesOnly is only cautious.
	final := !r.check.Always && cur.Final() && (r.check.FilesOnly || !cur.FilesOnly)
	if final && r.current(cur, spec) && !stale(cur) {
		return nil
	}

	repo := kube.Get[gitk8s.Repository](ctx, meta.Namespace, spec.Repository)
	if repo == nil {
		return fmt.Errorf("GitRepository %s/%s doesn't exist", meta.Namespace, spec.Repository)
	}
	r.once.Do(func() {
		r.cache = &gitk8s.Cache{Git: &r.cfg.Git, Dir: r.cfg.CacheDir}
		if r.check.Remote != nil {
			r.cache.Remote = func(ctx context.Context, repo *gitk8s.Repository) (git.Remote, error) {
				return r.check.Remote(ctx, r.cfg.CoreURL, repo)
			}
		}
	})
	in := &Input{Meta: meta, Spec: spec, Policy: *policy, Repository: repo, Previous: cur, identity: r.cfg.Identity, coreURL: r.cfg.CoreURL, check: &r.check, cache: r.cache, bases: &r.bases, same: &r.same}
	defer in.release()
	if final && !r.current(cur, spec) && cur.Scope == gitk8s.ScopeChange {
		if kept := r.keep(ctx, in, cur); kept != nil && !stale(kept) {
			*result = kept
			return nil
		}
	}

	res := &gitk8s.CheckResult{Commit: spec.Head, Scope: gitk8s.ScopeHead, FilesOnly: r.check.FilesOnly}
	if r.check.UsesParent || r.check.SameChange {
		res.Scope, res.ParentCommit = gitk8s.ScopeParent, spec.ParentHead
	}
	v, err := r.check.Run(ctx, in)
	if err != nil {
		res.State, res.Message, res.Notes = gitk8s.Error, truncate(err.Error()), notes(cur)
		*result = res
		return err
	}
	res.State, res.Message = v.State, truncate(v.Message)
	res.Outputs = truncateValues(v.Outputs, gitk8s.MaxOutputValueLength)
	res.Notes = truncateValues(v.Notes, gitk8s.MaxNoteValueLength)
	res.Pod = v.Pod
	r.record(ctx, in, v, res)
	reported, why := res, "the core program doesn't accept the check's result: "
	if v.Fix != "" {
		// If push doesn't push, it reports Failed with the Fixed result's
		// outputs, notes, and Pod, so checking the Fixed result covers that
		// one too.
		reported, why = fixed(res, v), "not pushing the fix because the core program wouldn't accept the Fixed result: "
	}
	if err := reported.Validate(); err != nil {
		// Running the check again returns the same result, so report why in
		// the result instead of failing the reconcile, which kube retries.
		res.State, res.Message, res.Outputs, res.Pod = gitk8s.Error, truncate(why+err.Error()), nil, ""
		if res.Validate() != nil {
			// The core program rejects the verdict's notes, so keep the
			// previous result's, such as how many times an agent ran, which
			// the next run counts from.
			res.Notes = notes(cur)
		}
		*result = res
		return nil
	}
	if v.Fix != "" {
		if err := r.push(ctx, in, v, res); err != nil {
			res.State, res.Message = gitk8s.Error, truncate(err.Error())
			*result = res
			return err
		}
	}
	*result = res
	return nil
}

// current reports whether a final result holds for the branch's heads,
// without reading the repository.
func (r *reconciler[V, P]) current(cur *gitk8s.CheckResult, spec *gitk8s.GitBranchSpec) bool {
	if cur.Commit != spec.Head {
		return false
	}
	switch cur.Scope {
	case gitk8s.ScopeHead:
		return !r.check.UsesParent && !r.check.SameChange
	case gitk8s.ScopeParent:
		return cur.ParentCommit == spec.ParentHead
	case gitk8s.ScopeChange:
		// A merge base is an ancestor of the head, so when the parent's
		// head is the merge base, it's still the head's merge base with
		// the parent.
		return cur.MergeBase == spec.ParentHead
	}
	return false
}

// keep checks a final result with a merge base, which current can't check
// without the repository. It returns cur if the branch's head and its merge
// base with the parent's head are still the result's, or, for a check with
// SameChange, a copy of cur for the branch's head if the head makes the
// same change. It returns nil if the check must run, including when it
// can't tell.
func (r *reconciler[V, P]) keep(ctx context.Context, in *Input, cur *gitk8s.CheckResult) *gitk8s.CheckResult {
	change, err := in.Change(ctx)
	if err != nil || change.Base == "" {
		return nil
	}
	last := git.Change{Base: cur.MergeBase, Head: cur.Commit}
	switch {
	case change == last:
		return cur
	case !r.check.SameChange || cur.State != gitk8s.Passed && cur.State != gitk8s.Failed:
		return nil
	}
	same, err := in.SameChange(ctx, last, change)
	if err != nil {
		slog.Warn("comparing changes failed, so running the check", "check", r.check.Name, "namespace", in.Meta.Namespace, "branch", in.Spec.Branch, "err", err)
	}
	if err != nil || !same {
		return nil
	}
	kept := *cur
	kept.Commit, kept.MergeBase, kept.Outputs, kept.Notes = change.Head, change.Base, maps.Clone(cur.Outputs), maps.Clone(cur.Notes)
	slog.Info("kept a result for the same change", "check", r.check.Name, "namespace", in.Meta.Namespace, "branch", in.Spec.Branch,
		"from", gitk8s.Short(last.Head), "to", gitk8s.Short(change.Head), "mergeBase", gitk8s.Short(change.Base))
	return &kept
}

// record sets res's scope to what v holds for besides the branch's head:
// the parent's head, or the head's change on top of its merge base with
// the parent's head. A verdict of a check with SameChange holds for the
// change if it's Passed or Failed, has no fix, doesn't use the parent, and
// the head has one merge base; otherwise it holds for the parent's head.
func (r *reconciler[V, P]) record(ctx context.Context, in *Input, v Verdict, res *gitk8s.CheckResult) {
	if v.UsesParent {
		res.Scope, res.ParentCommit = gitk8s.ScopeParent, in.Spec.ParentHead
	}
	switch {
	case !r.check.SameChange:
		if res.Scope == gitk8s.ScopeHead && v.MergeBase != "" {
			res.Scope, res.MergeBase = gitk8s.ScopeChange, v.MergeBase
		}
		return
	case r.check.UsesParent || v.UsesParent || v.Fix != "" || v.State != gitk8s.Passed && v.State != gitk8s.Failed:
		return
	}
	if change, err := in.Change(ctx); err == nil && change.Base != "" {
		res.Scope, res.ParentCommit, res.MergeBase = gitk8s.ScopeChange, "", change.Base
	}
}

// push pushes a verdict's fix if the policy and the branch's budget allow,
// and records the outcome in res.
func (r *reconciler[V, P]) push(ctx context.Context, in *Input, v Verdict, res *gitk8s.CheckResult) error {
	res.State = gitk8s.Failed
	if !in.Policy.MayPush {
		res.Message = truncate(v.Message + "; the policy doesn't let this check push the fix")
		return nil
	}
	local, err := in.Repo(ctx)
	if err != nil {
		return err
	}
	base, err := in.MergeBase(ctx)
	if err != nil {
		return err
	}
	n, err := local.CountFixerCommits(ctx, base, in.Spec.Head)
	if err != nil {
		return err
	}
	if limit := in.Spec.Merge.MaxCommits(); n >= limit {
		res.Message = truncate(fmt.Sprintf("%s; not pushing the fix because the branch already has %d automated commits, the limit", v.Message, n))
		return nil
	}
	remote, err := in.Remote(ctx)
	if err != nil {
		return err
	}
	err = local.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + in.Spec.Branch, New: v.Fix, Old: in.Spec.Head})
	if err != nil {
		// If the push was rejected because the branch moved since the
		// repository controller listed it, the next listing changes the
		// spec, which runs the check on the new head.
		return fmt.Errorf("pushing %s to %s: %w", gitk8s.Short(v.Fix), in.Spec.Branch, err)
	}
	slog.Info("pushed a fix", "check", r.check.Name, "namespace", in.Meta.Namespace, "branch", in.Spec.Branch, "from", gitk8s.Short(in.Spec.Head), "to", gitk8s.Short(v.Fix))
	kube.Eventf(ctx, kube.Normal, "PushedFix", "pushed %s to %s: %s", gitk8s.Short(v.Fix), in.Spec.Branch, v.Message)
	*res = *fixed(res, v)
	return nil
}

// fixed returns the result that push reports after it pushes v's fix.
func fixed(res *gitk8s.CheckResult, v Verdict) *gitk8s.CheckResult {
	f := *res
	f.State, f.Fix = gitk8s.Fixed, v.Fix
	f.Message = truncate(fmt.Sprintf("%s; pushed %s", v.Message, gitk8s.Short(v.Fix)))
	return &f
}

// Input is what a check sees of a branch.
type Input struct {
	Meta       *kube.ObjectMeta
	Spec       *gitk8s.GitBranchSpec
	Policy     gitk8s.CheckPolicy
	Repository *gitk8s.Repository
	// Previous is the check's last result, which can be for other commits.
	Previous *gitk8s.CheckResult

	identity git.Identity
	coreURL  string
	check    *Check
	cache    *gitk8s.Cache
	remote   *git.Remote
	local    *git.Repo
	unlock   func()
	fetched  bool
	bases    *memo[commitPair, []string]
	same     *memo[changePair, bool]
	key      **git.SigningKey
}

// MirrorURL returns the URL of the repository's copy on the core program's
// mirror, which the Pod that a Running verdict names can fetch from.
func (in *Input) MirrorURL() string {
	return strings.TrimSuffix(in.coreURL, "/") + gitk8s.MirrorPath(in.Repository.Namespace, in.Repository.Name)
}

// Remote returns the repository's URL and credentials, from Check.Remote.
func (in *Input) Remote(ctx context.Context) (git.Remote, error) {
	if in.remote == nil {
		if in.check.Remote == nil {
			return git.Remote{}, fmt.Errorf("the %s check can't reach the repository: set Check.Remote to mirror.Remote", in.check.Name)
		}
		r, err := in.check.Remote(ctx, in.coreURL, in.Repository)
		if err != nil {
			return r, err
		}
		in.remote = &r
	}
	return *in.remote, nil
}

// Repo fetches the branch and its parent into a local repository and
// returns it. Spec.Head and Spec.ParentHead are in the repository.
func (in *Input) Repo(ctx context.Context) (*git.Repo, error) {
	if in.fetched {
		return in.local, nil
	}
	remote, err := in.Remote(ctx)
	if err != nil {
		return nil, err
	}
	local, err := in.open(ctx)
	if err != nil {
		return nil, err
	}
	if err := local.Fetch(ctx, remote, in.Spec.Branch, in.Spec.Parent); err != nil {
		return nil, err
	}
	for _, sha := range []string{in.Spec.Head, in.Spec.ParentHead} {
		if ok, err := local.HasCommit(ctx, sha); err != nil || !ok {
			return nil, cmp.Or(err, fmt.Errorf("fetched %s and %s but don't have %s; the branches moved, so waiting for the repository controller to list them again", in.Spec.Branch, in.Spec.Parent, gitk8s.Short(sha)))
		}
	}
	in.fetched = true
	return local, nil
}

// open opens the local repository without fetching. It stays locked until
// the reconcile ends.
func (in *Input) open(ctx context.Context) (*git.Repo, error) {
	if in.local == nil {
		local, unlock, err := in.cache.Open(ctx, in.Repository)
		if err != nil {
			return nil, err
		}
		in.local, in.unlock = local, unlock
	}
	return in.local, nil
}

// have returns the local repository once it has commits. It fetches the
// branch and its parent for a commit that the repository doesn't have,
// and then the commit by name. If the remote doesn't have the commit, the
// error wraps ErrUnknownCommit.
func (in *Input) have(ctx context.Context, commits ...string) (*git.Repo, error) {
	local, err := in.open(ctx)
	if err != nil {
		return nil, err
	}
	missing := func() ([]string, error) {
		var out []string
		for _, c := range commits {
			ok, err := local.HasCommit(ctx, c)
			if err != nil {
				return nil, err
			}
			if !ok && !slices.Contains(out, c) {
				out = append(out, c)
			}
		}
		return out, nil
	}
	gone, err := missing()
	if err == nil && len(gone) > 0 && !in.fetched {
		if _, err = in.Repo(ctx); err == nil {
			gone, err = missing()
		}
	}
	if err != nil || len(gone) == 0 {
		return local, err
	}
	remote, err := in.Remote(ctx)
	if err != nil {
		return nil, err
	}
	fetchErr := local.FetchCommits(ctx, remote, gone...)
	if gone, err = missing(); err != nil || len(gone) == 0 {
		return local, err
	}
	var gitErr *git.Error
	if fetchErr == nil || errors.As(fetchErr, &gitErr) && strings.Contains(gitErr.Stderr, "not our ref") {
		return nil, fmt.Errorf("%w: %s", ErrUnknownCommit, gitk8s.Short(gone[0]))
	}
	return nil, fetchErr
}

// repoKey names the repository in memo keys, which hold commits by name.
func (in *Input) repoKey() string {
	return in.Repository.Namespace + "/" + in.Repository.Name + " " + in.Repository.Spec.URL
}

// mergeBases returns every best common ancestor of two commits, as
// git.Repo.MergeBases does, reading the local repository before it fetches.
func (in *Input) mergeBases(ctx context.Context, a, b string) ([]string, error) {
	key := commitPair{in.repoKey(), a, b}
	if bases, ok := in.bases.get(key); ok {
		return bases, nil
	}
	local, err := in.open(ctx)
	if err != nil {
		return nil, err
	}
	bases, err := local.MergeBases(ctx, a, b)
	if err != nil {
		if local, err = in.have(ctx, a, b); err != nil {
			return nil, err
		}
		if bases, err = local.MergeBases(ctx, a, b); err != nil {
			return nil, err
		}
	}
	in.bases.put(key, bases)
	return bases, nil
}

// MergeBase returns the best common ancestor of the branch's head and the
// parent's head, or "" if they have none. When they have more than one, it
// returns one of them, as git merge-base does.
func (in *Input) MergeBase(ctx context.Context) (string, error) {
	bases, err := in.mergeBases(ctx, in.Spec.Head, in.Spec.ParentHead)
	if err != nil || len(bases) == 0 {
		return "", err
	}
	return bases[0], nil
}

// Change returns what the branch's head changes on top of its merge base
// with the parent's head.
func (in *Input) Change(ctx context.Context) (git.Change, error) {
	return in.ChangeOf(ctx, in.Spec.Head)
}

// ChangeOf returns what a commit changes on top of its merge base with the
// parent's head. The commit can be one that no branch has, such as the
// branch's head before a rebase. If the repository doesn't have it, the
// error wraps ErrUnknownCommit.
func (in *Input) ChangeOf(ctx context.Context, commit string) (git.Change, error) {
	if !git.IsObjectName(commit) {
		return git.Change{}, fmt.Errorf("%q isn't a full commit SHA", commit)
	}
	bases, err := in.mergeBases(ctx, commit, in.Spec.ParentHead)
	if err != nil {
		return git.Change{}, err
	}
	c := git.Change{Head: commit}
	if len(bases) == 1 {
		c.Base = bases[0]
	}
	return c, nil
}

// SameChange reports whether change b makes the same change as change a,
// as git.Repo.SameChange compares them, so that a result for a's head
// holds for b's head. It fetches commits that the local repository
// doesn't have, and remembers the answer for the same changes.
func (in *Input) SameChange(ctx context.Context, a, b git.Change) (bool, error) {
	if a.Base == "" || b.Base == "" {
		return false, nil
	}
	key := changePair{in.repoKey(), a, b}
	if same, ok := in.same.get(key); ok {
		return same, nil
	}
	local, err := in.open(ctx)
	if err != nil {
		return false, err
	}
	same, err := local.SameChange(ctx, a, b)
	if err != nil {
		if local, err = in.have(ctx, a.Base, a.Head, b.Base, b.Head); err != nil {
			return false, err
		}
		if same, err = local.SameChange(ctx, a, b); err != nil {
			return false, err
		}
	}
	in.same.put(key, same)
	return same, nil
}

// CommitTree makes a commit in Repo's repository, with the controller's
// identity as its author and committer. If the check's policy lets it
// push, CommitTree signs the commit with the key from Check.SigningKey, if
// the repository names one. Otherwise the framework doesn't push the
// commit, so CommitTree neither reads the key nor signs the commit.
func (in *Input) CommitTree(ctx context.Context, tree string, parents []string, message string, unix int64) (string, error) {
	local, key, err := in.committer(ctx)
	if err != nil {
		return "", err
	}
	return local.CommitTree(ctx, tree, parents, message, in.identity, unix, key)
}

// Replay makes a commit in Repo's repository that replays commit onto
// parent with tree, as git.Repo.Replay does, with the controller's identity
// as its committer. It signs the commit as CommitTree does. When a new
// commit can't take commit's author, Replay makes no commit and returns
// the problem, as git.Repo.Replay does.
func (in *Input) Replay(ctx context.Context, commit, parent, tree string) (sha, problem string, err error) {
	local, key, err := in.committer(ctx)
	if err != nil {
		return "", "", err
	}
	return local.Replay(ctx, commit, parent, tree, in.identity, key)
}

// committer returns Repo's repository, and the key that signs the commits
// that the check makes there, which is nil unless the check's policy lets
// it push. It reads the key at most once.
func (in *Input) committer(ctx context.Context) (*git.Repo, *git.SigningKey, error) {
	if in.check.SigningKey == nil {
		return nil, nil, fmt.Errorf("the %s check can't make commits: set Check.SigningKey to signing.Key", in.check.Name)
	}
	local, err := in.Repo(ctx)
	if err != nil || !in.Policy.MayPush {
		return local, nil, err
	}
	if in.key == nil {
		key, err := in.check.SigningKey(ctx, in.Repository)
		if err != nil {
			return nil, nil, err
		}
		in.key = &key
	}
	return local, *in.key, nil
}

func (in *Input) release() {
	if in.unlock != nil {
		in.unlock()
	}
}

// truncate keeps messages to the size that the core program accepts.
func truncate(s string) string { return shorten(s, gitk8s.MaxMessageLength) }

// truncateValues keeps output or note values to n bytes, the most that the
// core program accepts.
func truncateValues(values map[string]string, n int) map[string]string {
	if values == nil {
		return nil
	}
	out := make(map[string]string, len(values))
	for k, v := range values {
		out[k] = shorten(v, n)
	}
	return out
}

// notes returns a copy of a result's notes, or nil for no result.
func notes(r *gitk8s.CheckResult) map[string]string {
	if r == nil {
		return nil
	}
	return maps.Clone(r.Notes)
}

// shorten returns s as valid UTF-8 of at most n bytes, ending in "..." if
// it's cut. The core program measures a result after decoding it from JSON,
// which turns each invalid byte into a three-byte replacement character.
func shorten(s string, n int) string {
	s = strings.ToValidUTF8(s, "\uFFFD")
	if len(s) <= n {
		return s
	}
	n -= len("...")
	for n > 0 && !utf8.RuneStart(s[n]) {
		n--
	}
	return s[:n] + "..."
}

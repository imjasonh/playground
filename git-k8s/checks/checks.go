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
	"flag"
	"fmt"
	"log/slog"
	"maps"
	"net/http"
	"os"
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
	// FilesOnly says that the check's result for the branch's head also
	// holds for any commit with the same files that builds on the same
	// parent head, because the result doesn't depend on the branch's
	// commits, such as their messages, authors, or signatures. Only such
	// results count for the commits that squash and rebase landings make.
	// For a check without it, the merge controller pushes those commits to
	// the branch, and the check runs on them before they land.
	FilesOnly bool
	// Always runs the check on every reconcile, instead of only when the
	// heads change. Use it for checks that read only the GitBranch object.
	Always bool
	// Stale, when set, reports whether a final result for the branch's
	// current heads needs the check to run again anyway, for a check whose
	// result depends on more than the heads. It can read objects with
	// kube.Get, and a change to one of them calls it again.
	Stale func(ctx context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool
	// Remote returns a repository's URL and credentials. A check that calls
	// Input.Repo or returns a Fix sets it to mirror.Remote, which reaches
	// the repository's copy on the mirror. A check that leaves it nil
	// doesn't link that package, so its program gets no token for the
	// mirror.
	Remote func(context.Context, *gitk8s.Repository) (git.Remote, error)
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
// message and output values to fit the core program's limits, and reports
// an Error result instead of a verdict that the core program doesn't
// accept, such as one with more than gitk8s.MaxOutputs outputs.
type Verdict struct {
	// State is Passed, Failed, or Running.
	State   string
	Message string
	Outputs map[string]string
	// Fix, when set, is a commit that fixes what the check found, such as a
	// commit on top of the branch's head. The framework moves the branch to
	// it with a lease on the head, even if it doesn't contain the head, when
	// the check's policy allows and the branch has automated commits left,
	// and reports Fixed, with the commit in the output fix; otherwise it
	// reports Failed. It reports Error instead, and doesn't move the branch,
	// if the core program wouldn't accept the Fixed result.
	Fix string
}

// Pass returns a passing verdict.
func Pass(format string, args ...any) Verdict {
	return Verdict{State: gitk8s.Passed, Message: fmt.Sprintf(format, args...)}
}

// Fail returns a failing verdict.
func Fail(format string, args ...any) Verdict {
	return Verdict{State: gitk8s.Failed, Message: fmt.Sprintf(format, args...)}
}

// Config holds what check controllers need to work with git and to send
// results.
type Config struct {
	Git      git.Git
	CacheDir string
	Identity git.Identity
	// ResultsURL is the core program's results endpoint.
	ResultsURL string
}

// AddFlags registers flags that set c: -git, -cache-dir, -identity-name,
// -identity-email, and -results-url.
func (c *Config) AddFlags(fs *flag.FlagSet) {
	fs.StringVar(&c.Git.Bin, "git", "git", "git executable")
	fs.StringVar(&c.CacheDir, "cache-dir", gitk8s.DefaultCacheDir, "writable directory for local copies of repositories")
	fs.StringVar(&c.Identity.Name, "identity-name", "git-k8s", "author and committer name of commits that the controller pushes")
	fs.StringVar(&c.Identity.Email, "identity-email", "git-k8s@users.noreply.github.com", "author and committer email of commits that the controller pushes")
	fs.StringVar(&c.ResultsURL, "results-url", defaultResultsURL, "URL of the core program's results endpoint")
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
	parentCommit := ""
	if r.check.UsesParent {
		parentCommit = spec.ParentHead
	}
	cur := *result
	// A result with filesOnly from before the check stopped setting
	// FilesOnly must not count for a squashed or rebased commit, so the
	// check runs again. A result without filesOnly is only cautious.
	if !r.check.Always && cur.Final() && cur.Commit == spec.Head && cur.ParentCommit == parentCommit && (r.check.FilesOnly || !cur.FilesOnly) &&
		(r.check.Stale == nil || !r.check.Stale(ctx, meta, spec, cur)) {
		return nil
	}

	repo := kube.Get[gitk8s.Repository](ctx, meta.Namespace, spec.Repository)
	if repo == nil {
		return fmt.Errorf("GitRepository %s/%s doesn't exist", meta.Namespace, spec.Repository)
	}
	r.once.Do(func() { r.cache = &gitk8s.Cache{Git: &r.cfg.Git, Dir: r.cfg.CacheDir} })
	in := &Input{Meta: meta, Spec: spec, Policy: *policy, Repository: repo, Previous: cur, identity: r.cfg.Identity, check: &r.check, cache: r.cache}
	defer in.release()

	res := &gitk8s.CheckResult{Commit: spec.Head, ParentCommit: parentCommit, FilesOnly: r.check.FilesOnly}
	v, err := r.check.Run(ctx, in)
	if err != nil {
		res.State, res.Message = gitk8s.Error, truncate(err.Error())
		*result = res
		return err
	}
	res.State, res.Message, res.Outputs = v.State, truncate(v.Message), truncateOutputs(v.Outputs)
	reported, why := res, "the core program doesn't accept the check's result: "
	if v.Fix != "" {
		// If push doesn't push, it reports Failed with at most the Fixed
		// result's outputs, so checking the Fixed result covers that one too.
		reported, why = fixed(res, v), "not pushing the fix because the core program wouldn't accept the Fixed result: "
	}
	if err := reported.Validate(); err != nil {
		// Running the check again returns the same result, so report why in
		// the result instead of failing the reconcile, which kube retries.
		res.State, res.Message, res.Outputs = gitk8s.Error, truncate(why+err.Error()), nil
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
	f.State = gitk8s.Fixed
	f.Message = truncate(fmt.Sprintf("%s; pushed %s", v.Message, gitk8s.Short(v.Fix)))
	f.Outputs = maps.Clone(res.Outputs)
	if f.Outputs == nil {
		f.Outputs = map[string]string{}
	}
	f.Outputs["fix"] = v.Fix
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

	identity  git.Identity
	check     *Check
	cache     *gitk8s.Cache
	remote    *git.Remote
	local     *git.Repo
	unlock    func()
	mergeBase *string
	key       **git.SigningKey
}

// Remote returns the repository's URL and credentials, from Check.Remote.
func (in *Input) Remote(ctx context.Context) (git.Remote, error) {
	if in.remote == nil {
		if in.check.Remote == nil {
			return git.Remote{}, fmt.Errorf("the %s check can't reach the repository: set Check.Remote to mirror.Remote", in.check.Name)
		}
		r, err := in.check.Remote(ctx, in.Repository)
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
	if in.local != nil {
		return in.local, nil
	}
	remote, err := in.Remote(ctx)
	if err != nil {
		return nil, err
	}
	local, unlock, err := in.cache.Open(ctx, in.Repository)
	if err != nil {
		return nil, err
	}
	in.unlock = unlock
	if err := local.Fetch(ctx, remote, in.Spec.Branch, in.Spec.Parent); err != nil {
		return nil, err
	}
	for _, sha := range []string{in.Spec.Head, in.Spec.ParentHead} {
		if ok, err := local.HasCommit(ctx, sha); err != nil || !ok {
			return nil, cmp.Or(err, fmt.Errorf("fetched %s and %s but don't have %s; the branches moved, so waiting for the repository controller to list them again", in.Spec.Branch, in.Spec.Parent, gitk8s.Short(sha)))
		}
	}
	in.local = local
	return local, nil
}

// MergeBase returns the best common ancestor of the branch's head and the
// parent's head, or "" if they have none.
func (in *Input) MergeBase(ctx context.Context) (string, error) {
	if in.mergeBase == nil {
		local, err := in.Repo(ctx)
		if err != nil {
			return "", err
		}
		mb, err := local.MergeBase(ctx, in.Spec.Head, in.Spec.ParentHead)
		if err != nil {
			return "", err
		}
		in.mergeBase = &mb
	}
	return *in.mergeBase, nil
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

// truncateOutputs keeps output values to the size that the core program
// accepts.
func truncateOutputs(outputs map[string]string) map[string]string {
	if outputs == nil {
		return nil
	}
	out := make(map[string]string, len(outputs))
	for k, v := range outputs {
		out[k] = shorten(v, gitk8s.MaxOutputValueLength)
	}
	return out
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

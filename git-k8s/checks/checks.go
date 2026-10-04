// Package checks runs check controllers.
//
// A check controller reconciles GitBranch objects through its own view type,
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
// kube writes the status that a reconcile leaves with server-side apply, so
// each check controller manages exactly its own entry. Other checks' entries
// never pass through it, and because its cache doesn't decode them, their
// changes don't make it reconcile.
package checks

import (
	"cmp"
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"sync"

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
	// Always runs the check on every reconcile, instead of only when the
	// heads change. Use it for checks that read only the GitBranch object.
	Always bool
	// Remote returns a repository's URL and credentials. A check that calls
	// Input.Repo or returns a Fix sets it to mirror.Remote, which reaches
	// the repository's copy on the mirror. A check that leaves it nil
	// doesn't link that package, so its program gets no token for the
	// mirror.
	Remote func(context.Context, *gitk8s.Repository) (git.Remote, error)
	// Run examines the branch.
	Run func(ctx context.Context, in *Input) (Verdict, error)
}

// Verdict is the outcome of running a check.
type Verdict struct {
	// State is Passed, Failed, or Running.
	State   string
	Message string
	Outputs map[string]string
	// Fix, when set, is a commit on top of the branch's head that fixes
	// what the check found. The framework pushes it when the check's policy
	// allows and the branch has automated commits left, and reports Fixed;
	// otherwise it reports Failed.
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

// Config holds what check controllers need to work with git.
type Config struct {
	Git      git.Git
	CacheDir string
	Identity git.Identity
}

// AddFlags registers flags that set c: -git, -cache-dir, -identity-name,
// and -identity-email.
func (c *Config) AddFlags(fs *flag.FlagSet) {
	fs.StringVar(&c.Git.Bin, "git", "git", "git executable")
	fs.StringVar(&c.CacheDir, "cache-dir", gitk8s.DefaultCacheDir, "writable directory for local copies of repositories")
	fs.StringVar(&c.Identity.Name, "identity-name", "git-k8s", "author and committer name of commits that the controller pushes")
	fs.StringVar(&c.Identity.Email, "identity-email", "git-k8s@users.noreply.github.com", "author and committer email of commits that the controller pushes")
}

// Main runs a check controller with flags from Config.AddFlags and kube.Main.
func Main[V any, P interface {
	kube.Resource[V]
	View
}](check Check) {
	cfg := &Config{}
	cfg.AddFlags(flag.CommandLine)
	kube.Main(For[V, P](check, cfg))
}

// For returns a controller that runs check on every GitBranch whose merge
// policy lists it. The controller's name, and so its field manager, is
// check- followed by the check's name.
func For[V any, P interface {
	kube.Resource[V]
	View
}](check Check, cfg *Config, opts ...kube.Option) kube.Controller {
	return kube.For[V, P](NewReconciler[V, P](check, cfg), append([]kube.Option{kube.Named("check-" + check.Name)}, opts...)...)
}

// NewReconciler returns the reconciler that For runs, for tests that call
// Reconcile directly with a context from kube.Fake.
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
		// Leaving the entry empty removes it: this controller stops
		// managing a field it no longer applies.
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
	if !r.check.Always && cur.Final() && cur.Commit == spec.Head && cur.ParentCommit == parentCommit {
		return nil
	}

	repo := kube.Get[gitk8s.Repository](ctx, meta.Namespace, spec.Repository)
	if repo == nil {
		return fmt.Errorf("GitRepository %s/%s doesn't exist", meta.Namespace, spec.Repository)
	}
	r.once.Do(func() { r.cache = &gitk8s.Cache{Git: &r.cfg.Git, Dir: r.cfg.CacheDir} })
	in := &Input{Meta: meta, Spec: spec, Policy: *policy, Repository: repo, Identity: r.cfg.Identity, Previous: cur, check: &r.check, cache: r.cache}
	defer in.release()

	res := &gitk8s.CheckResult{Commit: spec.Head, ParentCommit: parentCommit}
	v, err := r.check.Run(ctx, in)
	if err != nil {
		res.State, res.Message = gitk8s.Error, truncate(err.Error())
		*result = res
		return err
	}
	res.State, res.Message, res.Outputs = v.State, truncate(v.Message), v.Outputs
	if v.Fix != "" {
		if err := r.push(ctx, in, v, res); err != nil {
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
	if errors.Is(err, git.ErrRejected) {
		// The branch moved since the repository controller listed it. The
		// next listing changes the spec, which runs the check again.
		return fmt.Errorf("pushing %s to %s: %w", gitk8s.Short(v.Fix), in.Spec.Branch, err)
	}
	if err != nil {
		return err
	}
	slog.Info("pushed a fix", "check", r.check.Name, "namespace", in.Meta.Namespace, "branch", in.Spec.Branch, "from", gitk8s.Short(in.Spec.Head), "to", gitk8s.Short(v.Fix))
	res.State = gitk8s.Fixed
	res.Message = truncate(fmt.Sprintf("%s; pushed %s", v.Message, gitk8s.Short(v.Fix)))
	if res.Outputs == nil {
		res.Outputs = map[string]string{}
	}
	res.Outputs["fix"] = v.Fix
	return nil
}

// Input is what a check sees of a branch.
type Input struct {
	Meta       *kube.ObjectMeta
	Spec       *gitk8s.GitBranchSpec
	Policy     gitk8s.CheckPolicy
	Repository *gitk8s.Repository
	// Identity is the author and committer for fix commits.
	Identity git.Identity
	// Previous is the check's last result, which can be for other commits.
	Previous *gitk8s.CheckResult

	check     *Check
	cache     *gitk8s.Cache
	remote    *git.Remote
	local     *git.Repo
	unlock    func()
	mergeBase *string
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

func (in *Input) release() {
	if in.unlock != nil {
		in.unlock()
	}
}

// truncate keeps messages to a size that fits comfortably in an object.
func truncate(s string) string {
	if len(s) > 1024 {
		return s[:1021] + "..."
	}
	return s
}

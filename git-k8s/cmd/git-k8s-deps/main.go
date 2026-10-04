// Command git-k8s-deps keeps the Go modules that repositories require up to
// date, with a branch for each update.
//
// The controller reconciles the GitBranch of each branch that a
// repository's rules name as the parent of branches under the controller's
// prefix, deps/ by default. Every -interval, it reads the parent's go.mod
// files and asks module proxies for newer releases of the modules that they
// require directly. For each module and major version with a release that's
// at least -min-age old, it runs go get in a sandboxed Pod and pushes the
// go.mod and go.sum files that go changed to its own branch, such as
// deps/go/example.com/greet@v1, as one commit on the parent. When a newer
// release comes out before the branch lands, the controller replaces the
// branch's commit with a lease, so each module keeps one branch. It also
// remakes a branch that falls behind the parent, unless checks pushed fixes
// to it that still merge cleanly.
//
// The Pod's first init container fetches the parent with the repository's
// credentials, the second runs go get without them, and a container from the
// agent runner image serves the result, which the controller fetches and
// checks as agent checks fetch an agent's result. kube deletes the Pod once
// the controller stops declaring it.
//
// Dependency branches go through the parent's merge policy like any other
// branch: check-deps has an agent fix the code when an update breaks the
// tests, and check-risk rates the update.
package main

import (
	"cmp"
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"maps"
	"path"
	"slices"
	"strings"
	"sync"
	"time"

	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
	"golang.org/x/mod/semver"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gomod"
	"github.com/imjasonh/playground/kube"
)

// Branch is the controller's view of a GitBranch. It has no status, so the
// controller writes none.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
}

// depsTrailer marks the commits that the controller pushes.
const depsTrailer = "Git-K8s-Deps"

// maxOwned is the most commits beyond the parent that a branch can have
// while the controller owns it: its update and up to 100 fixes, the most
// that maxAutomatedCommits allows.
const maxOwned = 101

// How long the controller waits to try again after fetching a result from a
// Pod fails, after a push is rejected because the branch moved, and after
// other errors.
const (
	fetchRetry = 5 * time.Second
	pushRetry  = 10 * time.Second
	errorRetry = time.Minute
)

type updater struct {
	cfg          checks.Config
	checkEmail   string
	prefix       string
	goProxy      string
	goSumDB      string
	goImage      string
	gitImage     string
	resultImage  string
	runtimeClass string
	timeout      time.Duration
	sourceSize   string
	goCacheSize  string
	maxPods      int
	interval     time.Duration
	minAge       time.Duration

	// now is time.Now, except in tests.
	now func() time.Time
	// resultPort is the port that result containers serve on, 8080 except
	// in tests.
	resultPort int

	once  sync.Once
	err   error
	proxy *proxy
	cache *gitk8s.Cache

	mu     sync.Mutex
	states map[kube.Key]*state
}

func (u *updater) addFlags(fs *flag.FlagSet) {
	u.cfg.AddFlags(fs)
	fs.StringVar(&u.checkEmail, "check-identity-email", "git-k8s@users.noreply.github.com", "committer email of the fixes that checks push, their -identity-email")
	fs.StringVar(&u.prefix, "prefix", "deps/", "branch-name prefix of the branches that the controller pushes, ending with /")
	fs.StringVar(&u.goProxy, "goproxy", "https://proxy.golang.org", "comma-separated URLs of the module proxies to read modules from")
	fs.StringVar(&u.goSumDB, "gosumdb", "sum.golang.org", "GOSUMDB for go get, or off")
	fs.StringVar(&u.goImage, "go-image", "cgr.dev/chainguard/go:latest", "image that runs go get; it needs go, git, sh, base64, sha256sum, tail, and cut")
	fs.StringVar(&u.gitImage, "git-image", "cgr.dev/chainguard/git:latest", "image that fetches the source; it needs git and sh")
	fs.StringVar(&u.resultImage, "result-image", "", "image that serves the result, built from agent/runner/Dockerfile (required)")
	fs.StringVar(&u.runtimeClass, "runtime-class", "", "RuntimeClass for update Pods, such as gvisor")
	fs.DurationVar(&u.timeout, "timeout", 15*time.Minute, "longest that an update Pod can run")
	fs.StringVar(&u.sourceSize, "source-size", "2Gi", "most disk space that an update Pod's copy of the repository can use")
	fs.StringVar(&u.goCacheSize, "go-cache-size", "4Gi", "most disk space that an update Pod's Go module and build caches can use")
	fs.IntVar(&u.maxPods, "max-pods", 10, "most update Pods to run at once, in all namespaces; 0 means no limit")
	fs.DurationVar(&u.interval, "interval", time.Hour, "how often to look for new versions")
	fs.DurationVar(&u.minAge, "min-age", 72*time.Hour, "how old a version must be, both by the time that the module proxy reports for it and since the controller first saw it, before the controller updates to it")
}

// setup checks the flags once.
func (u *updater) setup() error {
	u.once.Do(func() { u.err = u.init() })
	return u.err
}

func (u *updater) init() error {
	switch {
	case !strings.HasSuffix(u.prefix, "/") || !git.ValidBranch(u.prefix+"go"):
		return fmt.Errorf("-prefix is %q, but it must be a branch-name prefix that ends with /, such as deps/", u.prefix)
	case u.resultImage == "":
		return errors.New("set -result-image to the image that agent/runner/Dockerfile builds")
	case u.goImage == "" || u.gitImage == "" || u.goSumDB == "":
		return errors.New("-go-image, -git-image, and -gosumdb need values")
	case u.timeout < time.Second || u.interval < time.Second || u.minAge < 0:
		return errors.New("-timeout and -interval must be at least 1s, and -min-age can't be negative")
	case parseSize(u.sourceSize) == 0:
		return fmt.Errorf("-source-size is %q, but it must be a size such as 2Gi", u.sourceSize)
	case parseSize(u.goCacheSize) == 0:
		return fmt.Errorf("-go-cache-size is %q, but it must be a size such as 4Gi", u.goCacheSize)
	case u.cfg.Identity.Written().Email == "" || git.Identity{Email: u.checkEmail}.Written().Email == "":
		return errors.New("-identity-email and -check-identity-email need values")
	}
	urls, err := parseProxies(u.goProxy)
	if err != nil {
		return err
	}
	u.proxy = newProxy(urls, u.interval/2, u.clock)
	u.cache = &gitk8s.Cache{Git: &u.cfg.Git, Dir: u.cfg.CacheDir}
	return nil
}

func (u *updater) clock() time.Time {
	if u.now != nil {
		return u.now()
	}
	return time.Now()
}

func (u *updater) port() int { return cmp.Or(u.resultPort, 8080) }

// moduleMajor is a module at one major version, which gets one branch.
type moduleMajor struct {
	path, major string
}

// branch returns the name of the module's branch. Module paths can't hold
// @, so no branch name is a directory of another, which git can't store.
func (m moduleMajor) branch(prefix string) string {
	return prefix + "go/" + m.path + "@" + m.major
}

func compareModules(a, b moduleMajor) int {
	return cmp.Or(strings.Compare(a.path, b.path), strings.Compare(a.major, b.major))
}

// update updates a module to version in the go.mod files in from, which
// maps each file's directory to the version that it requires.
type update struct {
	module, version string
	from            map[string]string
}

func (up update) key() module.Version { return module.Version{Path: up.module, Version: up.version} }

// outcome is what an update Pod reported for an update: the go.mod and
// go.sum files that go changed, by path, or why the update failed.
type outcome struct {
	files map[string][]byte
	err   string
	at    time.Time
}

// state is what the controller remembers about a parent between
// reconciles.
type state struct {
	// head is the parent's head. The outcomes are for updates on it.
	head     string
	outcomes map[module.Version]*outcome
	// attempt goes up when an update fails, so that trying again starts a
	// new Pod.
	attempt int
}

// stateFor returns what the controller remembers about a parent, without
// outcomes from before the parent moved to head.
func (u *updater) stateFor(key kube.Key, head string) *state {
	u.mu.Lock()
	defer u.mu.Unlock()
	if u.states == nil {
		u.states = map[kube.Key]*state{}
	}
	st := u.states[key]
	if st == nil {
		st = &state{}
		u.states[key] = st
	}
	if st.head != head {
		st.head, st.outcomes = head, map[module.Version]*outcome{}
	}
	return st
}

func (u *updater) forget(key kube.Key) {
	u.mu.Lock()
	defer u.mu.Unlock()
	delete(u.states, key)
}

// change creates, replaces, or deletes a branch. old is the head that the
// branch must have, or "" if it must not exist. A change without an update
// deletes the branch.
type change struct {
	branch, old string
	up          update
}

func (u *updater) Reconcile(ctx context.Context, b *Branch) error {
	if err := u.setup(); err != nil {
		return kube.Permanent(err)
	}
	parent := b.Spec.Branch
	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	if repo == nil || !u.isParent(repo.Spec.Branches, parent) {
		u.forget(b.Key())
		return nil
	}
	kube.RequeueAfter(ctx, u.interval)
	log := slog.With("namespace", b.Namespace, "repository", repo.Name, "parent", parent)

	remote, err := credentials.Remote(ctx, repo)
	if err != nil {
		return err
	}
	heads, err := u.cfg.Git.LsRemote(ctx, remote)
	if err != nil {
		return err
	}
	parentHead := heads[parent]
	if parentHead == "" {
		u.forget(b.Key())
		return nil
	}
	existing := u.branches(repo.Spec.Branches, parent, heads)
	local, unlock, err := u.cache.Open(ctx, repo)
	if err != nil {
		return err
	}
	defer unlock()
	names := []string{parent}
	for m := range existing {
		names = append(names, m.branch(u.prefix))
	}
	if err := fetchMissing(ctx, local, remote, heads, names); err != nil {
		return err
	}
	mods, err := readModules(ctx, local, parentHead, log)
	if err != nil {
		return err
	}
	targets, failed := u.discover(ctx, repo.Spec.Branches, parent, requirements(mods), log)
	writes, deletes, err := u.plan(ctx, local, parentHead, maxCommits(repo.Spec.Branches, parent), targets, failed, existing)
	if err != nil {
		return err
	}

	// From here on, errors are logged instead of returned, so that kube
	// still applies the Pod that the reconcile declares.
	st := u.stateFor(b.Key(), parentHead)
	u.runPod(ctx, b, repo, st, writes, log)
	for _, w := range writes {
		u.write(ctx, local, remote, mods, st, w, log)
	}
	for _, d := range deletes {
		if err := u.push(ctx, local, remote, d.branch, "", d.old); err != nil {
			u.pushFailed(ctx, log, d.branch, err)
			continue
		}
		log.Info("deleted a branch that has no update left to make", "branch", d.branch, "head", gitk8s.Short(d.old))
	}
	return nil
}

// isParent reports whether a rule makes branch the parent of branches under
// the prefix.
func (u *updater) isParent(rules []gitk8s.BranchRule, branch string) bool {
	return !strings.HasPrefix(branch, u.prefix) && slices.ContainsFunc(rules, func(r gitk8s.BranchRule) bool {
		return r.Parent == branch && strings.HasPrefix(r.Match, u.prefix)
	})
}

// governs reports whether the rule for a branch under the prefix makes it
// propose changes to parent. An earlier rule without that parent keeps the
// controller away from a module.
func (u *updater) governs(rules []gitk8s.BranchRule, branch, parent string) bool {
	r := gitk8s.FindRule(rules, branch)
	return r != nil && r.Parent == parent
}

// maxCommits returns how many automated commits the parent's merge policy
// allows on each of its branches.
func maxCommits(rules []gitk8s.BranchRule, parent string) int {
	var p *gitk8s.MergePolicy
	if r := gitk8s.FindRule(rules, parent); r != nil {
		p = r.Merge
	}
	return p.MaxCommits()
}

// branches returns the module of each branch that the controller manages
// for parent, and the branch's head.
func (u *updater) branches(rules []gitk8s.BranchRule, parent string, heads map[string]string) map[moduleMajor]string {
	out := map[moduleMajor]string{}
	for name, head := range heads {
		rest, ok := strings.CutPrefix(name, u.prefix+"go/")
		i := strings.LastIndex(rest, "@")
		if !ok || i < 0 {
			continue
		}
		m := moduleMajor{path: rest[:i], major: rest[i+1:]}
		if module.CheckPath(m.path) == nil && m.major != "" && semver.Major(m.major) == m.major && git.ValidBranch(name) && u.governs(rules, name, parent) {
			out[m] = head
		}
	}
	return out
}

// fetchMissing fetches the branches whose heads the local repository
// doesn't have.
func fetchMissing(ctx context.Context, local *git.Repo, remote git.Remote, heads map[string]string, branches []string) error {
	var missing []string
	for _, b := range branches {
		ok, err := local.HasCommit(ctx, heads[b])
		if err != nil {
			return err
		}
		if !ok {
			missing = append(missing, b)
		}
	}
	if len(missing) == 0 {
		return nil
	}
	if err := local.Fetch(ctx, remote, missing...); err != nil {
		return err
	}
	for _, b := range missing {
		if ok, err := local.HasCommit(ctx, heads[b]); err != nil || !ok {
			return cmp.Or(err, fmt.Errorf("fetched %s but don't have %s; the branch moved, so trying again", b, gitk8s.Short(heads[b])))
		}
	}
	return nil
}

// modFile is a go.mod file that the controller can update.
type modFile struct {
	data []byte
	file *modfile.File
}

// readModules reads the go.mod files in a commit that the controller can
// update, by directory. It skips files in testdata and vendor directories,
// in directories whose names hold characters other than letters, digits,
// dots, hyphens, and underscores, and in modules that vendor their
// dependencies, which go get doesn't update.
func readModules(ctx context.Context, repo *git.Repo, commit string, log *slog.Logger) (map[string]*modFile, error) {
	entries, err := repo.LsTree(ctx, commit)
	if err != nil {
		return nil, err
	}
	vendored := map[string]bool{}
	for _, e := range entries {
		if dir := path.Dir(e.Path); path.Base(e.Path) == "modules.txt" && path.Base(dir) == "vendor" {
			vendored[path.Dir(dir)] = true
		}
	}
	mods := map[string]*modFile{}
	for _, e := range entries {
		dir := path.Dir(e.Path)
		if e.Type != "blob" || e.Mode == "120000" || !gomod.IsModFile(e.Path) || !safeDir(dir) || vendored[dir] {
			continue
		}
		data, err := repo.ReadBlob(ctx, e.SHA)
		if err != nil {
			return nil, err
		}
		f, err := modfile.Parse(e.Path, data, nil)
		if err == nil && f.Module == nil {
			err = errors.New("it has no module line")
		}
		if err != nil {
			log.Warn("skipping a go.mod file that doesn't parse", "path", e.Path, "error", err)
			continue
		}
		mods[dir] = &modFile{data: data, file: f}
	}
	return mods, nil
}

// safeDir reports whether each element of dir, a directory in a
// repository, has only letters, digits, dots, hyphens, and underscores.
// Directories go into the update script and its JSON output unquoted.
func safeDir(dir string) bool {
	if dir == "." {
		return true
	}
	for part := range strings.SplitSeq(dir, "/") {
		if part == "" || part == "." || part == ".." || part[0] == '-' || strings.ContainsFunc(part, func(r rune) bool {
			return (r < 'a' || r > 'z') && (r < 'A' || r > 'Z') && (r < '0' || r > '9') && r != '.' && r != '-' && r != '_'
		}) {
			return false
		}
	}
	return true
}

// requirement is a module at one major version that go.mod files require
// directly. from maps each file's directory to the version that it
// requires, and excluded holds the versions that any go.mod file excludes.
type requirement struct {
	from     map[string]string
	excluded map[string]bool
}

// requirements returns the direct requirements of the go.mod files, other
// than modules that a file replaces.
func requirements(mods map[string]*modFile) map[moduleMajor]*requirement {
	excluded := map[string]map[string]bool{}
	for _, m := range mods {
		for _, x := range m.file.Exclude {
			if excluded[x.Mod.Path] == nil {
				excluded[x.Mod.Path] = map[string]bool{}
			}
			excluded[x.Mod.Path][x.Mod.Version] = true
		}
	}
	reqs := map[moduleMajor]*requirement{}
	for dir, m := range mods {
		for _, r := range m.file.Require {
			p, v := r.Mod.Path, r.Mod.Version
			if r.Indirect || module.Check(p, v) != nil || slices.ContainsFunc(m.file.Replace, func(rep *modfile.Replace) bool {
				return rep.Old.Path == p && (rep.Old.Version == "" || rep.Old.Version == v)
			}) {
				continue
			}
			key := moduleMajor{path: p, major: semver.Major(v)}
			if reqs[key] == nil {
				reqs[key] = &requirement{from: map[string]string{}, excluded: excluded[p]}
			}
			reqs[key].from[dir] = v
		}
	}
	return reqs
}

// discover returns the update that each module needs, and the modules whose
// versions the controller couldn't read.
func (u *updater) discover(ctx context.Context, rules []gitk8s.BranchRule, parent string, reqs map[moduleMajor]*requirement, log *slog.Logger) (map[moduleMajor]update, map[moduleMajor]bool) {
	targets, failed := map[moduleMajor]update{}, map[moduleMajor]bool{}
	for _, m := range slices.SortedFunc(maps.Keys(reqs), compareModules) {
		name := m.branch(u.prefix)
		if !git.ValidBranch(name) || !u.governs(rules, name, parent) {
			continue
		}
		r := reqs[m]
		version, wait, err := u.proxy.target(ctx, m.path, slices.Collect(maps.Values(r.from)), r.excluded, u.minAge)
		kube.RequeueAfter(ctx, wait)
		if err != nil {
			failed[m] = true
			log.Warn("reading a module's versions failed", "module", m.path, "error", err)
			if !errors.Is(err, errNotFound) {
				kube.RequeueAfter(ctx, errorRetry)
			}
			continue
		}
		if version == "" {
			continue
		}
		up := update{module: m.path, version: version, from: map[string]string{}}
		for dir, v := range r.from {
			if semver.Compare(v, version) < 0 {
				up.from[dir] = v
			}
		}
		targets[m] = up
	}
	return targets, failed
}

// plan returns the branches to create or replace with updates, and the
// branches to delete. It leaves alone the branches of modules whose
// versions it couldn't read, and branches with commits from people.
// maxCommits is how many automated commits the parent's merge policy
// allows on a branch.
func (u *updater) plan(ctx context.Context, repo *git.Repo, parentHead string, maxCommits int, targets map[moduleMajor]update, failed map[moduleMajor]bool, existing map[moduleMajor]string) (writes, deletes []change, err error) {
	all := map[moduleMajor]bool{}
	for m := range targets {
		all[m] = true
	}
	for m := range existing {
		all[m] = true
	}
	for _, m := range slices.SortedFunc(maps.Keys(all), compareModules) {
		head, exists := existing[m]
		up, wanted := targets[m]
		c := change{branch: m.branch(u.prefix), old: head, up: up}
		switch {
		case failed[m]:
			continue
		case !exists:
			if wanted {
				writes = append(writes, c)
			}
			continue
		}
		owned, fixes, err := u.ownership(ctx, repo, parentHead, head)
		switch {
		case err != nil:
			return nil, nil, err
		case !owned:
			continue
		case !wanted:
			deletes = append(deletes, change{branch: c.branch, old: head})
			continue
		}
		ok, err := current(ctx, repo, parentHead, head, up, fixes < maxCommits && fixes > 0)
		if err != nil {
			return nil, nil, err
		}
		if !ok {
			writes = append(writes, c)
		}
	}
	return writes, deletes, nil
}

// ownership reports whether every commit that a branch has and its parent
// doesn't is the controller's or a check's fix, and counts the fixes. The
// controller committed its commits, which end with its trailer, and a check
// committed each fix, which ends with the fixer trailer. Someone who amends
// or squashes those commits becomes their committer, so the branch is
// theirs.
func (u *updater) ownership(ctx context.Context, repo *git.Repo, parentHead, head string) (owned bool, fixes int, err error) {
	commits, err := repo.ListCommits(ctx, parentHead, head, maxOwned+1)
	if err != nil || len(commits) > maxOwned {
		return false, 0, err
	}
	mine, checks := u.cfg.Identity.Written().Email, git.Identity{Email: u.checkEmail}.Written().Email
	for _, c := range commits {
		switch {
		case c.Committer.Email == checks && hasTrailer(c, git.FixerTrailer):
			fixes++
		case c.Committer.Email != mine || !hasTrailer(c, depsTrailer):
			return false, 0, nil
		}
	}
	return true, fixes, nil
}

func hasTrailer(c git.ListedCommit, key string) bool {
	return slices.ContainsFunc(c.Trailers, func(t string) bool { return strings.HasPrefix(t, key+":") })
}

// current reports whether a branch's head already makes an update on the
// parent. The branch must contain the parent's head, so that it can
// fast-forward, unless keep is set: then it only has to merge cleanly with
// the parent, which check-base can merge in. Remaking the update would drop
// the fixes that checks such as check-deps pushed, so the controller sets
// keep for branches with fixes and automated commits left for the merge.
func current(ctx context.Context, repo *git.Repo, parentHead, head string, up update, keep bool) (bool, error) {
	entries, err := repo.LsTree(ctx, head)
	if err != nil {
		return false, err
	}
	blobs := map[string]string{}
	for _, e := range entries {
		if e.Type == "blob" && e.Mode != "120000" && path.Base(e.Path) == "go.mod" {
			blobs[e.Path] = e.SHA
		}
	}
	for dir := range up.from {
		p := path.Join(dir, "go.mod")
		sha, ok := blobs[p]
		if !ok {
			return false, nil
		}
		data, err := repo.ReadBlob(ctx, sha)
		if err != nil {
			return false, err
		}
		if f, err := modfile.Parse(p, data, nil); err != nil || !requires(f, up.module, up.version) {
			return false, nil
		}
	}
	ok, err := repo.IsAncestor(ctx, parentHead, head)
	if err != nil || ok || !keep {
		return ok, err
	}
	_, conflicts, err := repo.MergeTree(ctx, head, parentHead)
	return err == nil && len(conflicts) == 0, err
}

// requires reports whether f requires mod at exactly version.
func requires(f *modfile.File, mod, version string) bool {
	found := false
	for _, r := range f.Require {
		if r.Mod.Path == mod {
			if r.Mod.Version != version {
				return false
			}
			found = true
		}
	}
	return found
}

// runPod starts or follows the Pod that makes the updates that writes need
// and that have no outcome yet, and records the outcomes that it reports. A
// failed update gets no new Pod until -interval after it failed.
func (u *updater) runPod(ctx context.Context, b *Branch, repo *gitk8s.Repository, st *state, writes []change, log *slog.Logger) {
	now := u.clock()
	wanted := map[module.Version]bool{}
	for _, w := range writes {
		wanted[w.up.key()] = true
	}
	for k, o := range st.outcomes {
		retry := o.at.Add(u.interval)
		switch {
		case !wanted[k], o.err != "" && !now.Before(retry):
			delete(st.outcomes, k)
		case o.err != "":
			kube.RequeueAfter(ctx, retry.Sub(now))
		}
	}
	var pending []update
	for _, w := range writes {
		if st.outcomes[w.up.key()] == nil && len(pending) < maxBatch {
			pending = append(pending, w.up)
		}
	}
	if len(pending) == 0 {
		return
	}
	desired := u.pod(b, repo, st.head, st.attempt, pending)
	if n := u.unfinishedPods(ctx, b.Namespace, desired.Name); u.maxPods > 0 && n >= u.maxPods {
		// Listing the Pods runs this again when one of them finishes.
		kube.RequeueAfter(ctx, time.Minute)
		return
	}
	out := u.follow(ctx, desired, pending, log)
	if out == nil {
		return
	}
	failedAny := false
	for _, up := range pending {
		o := out[up.key()]
		o.at = now
		st.outcomes[up.key()] = o
		if o.err != "" {
			failedAny = true
			log.Warn("updating a module failed", "module", up.module, "version", up.version, "error", o.err)
		}
	}
	if failedAny {
		st.attempt++
	}
	// The next reconcile doesn't declare the Pod, so kube deletes it.
	kube.RequeueAfter(ctx, time.Second)
}

// write commits an update whose Pod succeeded and pushes it to its branch.
func (u *updater) write(ctx context.Context, local *git.Repo, remote git.Remote, mods map[string]*modFile, st *state, w change, log *slog.Logger) {
	o := st.outcomes[w.up.key()]
	if o == nil || o.err != "" {
		return
	}
	if err := checkResult(mods, w.up, o.files); err != nil {
		o.err, o.files, o.at = "the update Pod's result isn't valid: "+err.Error(), nil, u.clock()
		st.attempt++
		log.Warn("updating a module failed", "module", w.up.module, "version", w.up.version, "error", o.err)
		return
	}
	commit, err := u.commit(ctx, local, st.head, w.up, o.files)
	if err == nil && commit != w.old {
		err = u.push(ctx, local, remote, w.branch, commit, w.old)
	}
	if err != nil {
		u.pushFailed(ctx, log, w.branch, err)
		return
	}
	if commit != w.old {
		log.Info("pushed an update", "branch", w.branch, "module", w.up.module, "version", w.up.version, "from", gitk8s.Short(w.old), "to", gitk8s.Short(commit))
	}
}

// checkResult checks the go.mod files that an update Pod reported. Each
// must require the module at the update's version, and differ from the
// parent's only in its requirements and its go and toolchain lines, as go
// get changes them. go.sum files hold checksums that the go command checks
// when it builds the branch.
func checkResult(mods map[string]*modFile, up update, files map[string][]byte) error {
	for _, p := range slices.Sorted(maps.Keys(files)) {
		if path.Base(p) != "go.mod" {
			continue
		}
		old := mods[path.Dir(p)]
		if old == nil {
			return fmt.Errorf("the parent has no %s to update", p)
		}
		f, err := modfile.Parse(p, files[p], nil)
		if err != nil {
			return err
		}
		o := old.file
		switch {
		case f.Module == nil || f.Module.Mod != o.Module.Mod:
			return fmt.Errorf("%s changes the module path", p)
		case !requires(f, up.module, up.version):
			return fmt.Errorf("%s doesn't require %s %s", p, up.module, up.version)
		case !sameDirectives(o.Replace, f.Replace, func(r *modfile.Replace) [2]module.Version { return [2]module.Version{r.Old, r.New} }):
			return fmt.Errorf("%s changes replace directives", p)
		case !sameDirectives(o.Exclude, f.Exclude, func(e *modfile.Exclude) module.Version { return e.Mod }):
			return fmt.Errorf("%s changes exclude directives", p)
		case !sameDirectives(o.Retract, f.Retract, func(r *modfile.Retract) [3]string { return [3]string{r.Low, r.High, r.Rationale} }):
			return fmt.Errorf("%s changes retract directives", p)
		case !sameDirectives(o.Tool, f.Tool, func(t *modfile.Tool) string { return t.Path }):
			return fmt.Errorf("%s changes tool directives", p)
		case !sameDirectives(o.Godebug, f.Godebug, func(g *modfile.Godebug) [2]string { return [2]string{g.Key, g.Value} }):
			return fmt.Errorf("%s changes godebug directives", p)
		case !sameDirectives(o.Ignore, f.Ignore, func(i *modfile.Ignore) string { return i.Path }):
			return fmt.Errorf("%s changes ignore directives", p)
		}
	}
	return nil
}

// sameDirectives reports whether two lists of directives hold the same
// directives in any order. go get sorts each block of directives and drops
// repeated ones.
func sameDirectives[T any, K comparable](a, b []T, key func(T) K) bool {
	set := func(s []T) map[K]bool {
		m := map[K]bool{}
		for _, d := range s {
			m[key(d)] = true
		}
		return m
	}
	return maps.Equal(set(a), set(b))
}

// commit makes the commit on the parent's head that writes an update's
// files. The same update on the same head always makes the same commit.
func (u *updater) commit(ctx context.Context, repo *git.Repo, parentHead string, up update, files map[string][]byte) (string, error) {
	c, err := repo.Commit(ctx, parentHead)
	if err != nil {
		return "", err
	}
	var changed []agent.File
	for _, p := range slices.Sorted(maps.Keys(files)) {
		changed = append(changed, agent.File{Path: p, Mode: "100644", Content: files[p]})
	}
	tree, err := agent.ApplyFiles(ctx, repo, c.Tree, changed)
	if err != nil {
		return "", err
	}
	return repo.CommitTree(ctx, tree, []string{parentHead}, message(up), u.cfg.Identity, c.Time)
}

// message returns the commit message of an update.
func message(up update) string {
	var b strings.Builder
	fmt.Fprintf(&b, "Update %s to %s\n\n", up.module, up.version)
	for _, dir := range slices.Sorted(maps.Keys(up.from)) {
		fmt.Fprintf(&b, "Update %s from %s to %s in %s.\n", up.module, up.from[dir], up.version, path.Join(dir, "go.mod"))
	}
	fmt.Fprintf(&b, "\n%s: go %s %s\n", depsTrailer, up.module, up.version)
	return b.String()
}

// push updates or deletes a branch with a lease on old. It refuses branches
// outside the prefix, because the repository's credentials can push to any
// branch.
func (u *updater) push(ctx context.Context, repo *git.Repo, remote git.Remote, branch, commit, old string) error {
	if !strings.HasPrefix(branch, u.prefix) || !git.ValidBranch(branch) {
		return fmt.Errorf("not pushing %q, which isn't a branch under %s", branch, u.prefix)
	}
	return repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/" + branch, New: commit, Old: old})
}

func (u *updater) pushFailed(ctx context.Context, log *slog.Logger, branch string, err error) {
	if errors.Is(err, git.ErrRejected) {
		log.Info("not pushing a branch that moved", "branch", branch)
		kube.RequeueAfter(ctx, pushRetry)
		return
	}
	log.Warn("pushing a branch failed", "branch", branch, "error", err)
	kube.RequeueAfter(ctx, errorRetry)
}

func main() {
	u := &updater{}
	u.addFlags(flag.CommandLine)
	kube.Main(kube.For[Branch](u, kube.Named("deps")))
}

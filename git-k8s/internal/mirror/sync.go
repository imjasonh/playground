package mirror

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"log/slog"
	"maps"
	"slices"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// SyncOptions say what Sync does besides comparing the copy with the
// external repository's branches as it last fetched them.
type SyncOptions struct {
	// Fetch fetches the external repository's branches first. Sync also
	// fetches when the copy is new, hasn't fetched yet, or has a new URL.
	Fetch bool
	// Push pushes the branches that changed only in the copy.
	Push bool
	// Final syncs a copy that's about to be deleted. Sync then doesn't
	// create the copy, and does nothing if the copy never fetched.
	Final bool
	// Remote returns the external repository's URL and credentials. Sync
	// calls it at most once, and only to fetch or push.
	Remote func() (git.Remote, error)
}

// Report is what Sync found.
type Report struct {
	// Heads maps each of the copy's branches to its commit.
	Heads map[string]string
	// Fetched reports whether Sync fetched the external repository.
	Fetched bool
	// Pending lists, sorted, the branches whose changes in the copy the
	// external repository doesn't have yet.
	Pending []string
	// Diverged maps each branch that diverged, as Mirror.Divergence says,
	// to the external repository's head, or to "" if the external
	// repository deleted the branch.
	Diverged map[string]string
	// Failed maps each branch whose heads Sync couldn't compare to why,
	// such as git timing out. Sync leaves such a branch as it is on each
	// side, and still syncs the other branches.
	Failed map[string]error
	// Unapplied maps each branch whose refs Sync couldn't update in the
	// copy to why, such as the external repository having a branch a/b
	// while the copy has a branch a, which git doesn't allow in one
	// repository. Sync still syncs the other branches, and the next sync
	// tries again.
	Unapplied map[string]error
	// Err says why Sync couldn't fetch from or push to the external
	// repository.
	Err error
}

// Sync brings repo's copy and the external repository together, creating
// the copy if it doesn't exist. For each branch, it pushes a change made
// only in the copy, takes a change made only in the external repository,
// and leaves a branch that changed in both as it is on each side. Unless
// the sync is final, Sync then runs git's maintenance on the copy, which
// packs its objects when it needs that.
//
// Sync returns an error, and no report, when it has no branches to report:
// the copy hasn't fetched the external repository yet, and the error wraps
// ErrNotSynced, or local git failed. Failing to fetch from or push to the
// external repository after the copy has fetched once only sets the
// report's Err, failing to compare one branch's heads only adds the branch
// to the report's Failed, and failing to update one branch's refs only adds
// the branch to the report's Unapplied.
func (m *Mirror) Sync(ctx context.Context, repo *gitk8s.Repository, o SyncOptions) (*Report, error) {
	e := m.entry(repo)
	e.syncing.Lock()
	defer e.syncing.Unlock()
	m.removeStaleLocks(e.dir)
	refetch, err := m.load(ctx, e, repo, !o.Final)
	switch {
	case o.Final && errors.Is(err, ErrNotSynced):
		return &Report{}, nil
	case err != nil:
		return nil, err
	}
	e.mu.RLock()
	defer e.mu.RUnlock()
	if o.Final && !e.seeded.Load() {
		return &Report{}, nil
	}

	s := &syncer{repo: e.repo, remote: sync.OnceValues(remoteOrError(o.Remote)), memo: &e.memo, timeout: m.compareLimit()}
	rep := &Report{}
	if o.Fetch || refetch || !e.seeded.Load() {
		if err := s.fetch(ctx); err != nil && !e.seeded.Load() {
			return nil, fmt.Errorf("%w: %w", ErrNotSynced, err)
		} else if err != nil {
			rep.Err = err
		}
		rep.Fetched = rep.Err == nil
	}
	for attempt := 1; rep.Err == nil; attempt++ {
		branches, err := s.plan(ctx)
		if err != nil {
			return nil, err
		}
		if rep.Unapplied, err = s.applyLocal(ctx, branches); err != nil {
			return nil, err
		}
		if err := e.markSeeded(ctx); err != nil {
			return nil, err
		}
		if !o.Push {
			break
		}
		rejected, unrecorded, err := s.push(ctx, branches)
		maps.Copy(rep.Unapplied, unrecorded)
		if err != nil || len(rejected) == 0 {
			rep.Err = err
			break
		}
		if attempt == 2 {
			rep.Err = refused(rejected)
			break
		}
		// The external repository changed since the fetch, so the leases
		// failed. Look again.
		if rep.Err = s.fetch(ctx); rep.Err == nil {
			rep.Fetched = true
		}
	}

	branches, err := s.plan(ctx)
	if err != nil {
		return nil, err
	}
	rep.Heads, rep.Diverged, rep.Failed = map[string]string{}, map[string]string{}, map[string]error{}
	for _, b := range branches {
		if b.m != "" {
			rep.Heads[b.name] = b.m
		}
		switch b.act {
		case push:
			rep.Pending = append(rep.Pending, b.name)
		case diverged:
			rep.Diverged[b.name] = b.d
		case failed:
			rep.Failed[b.name] = b.err
		}
	}
	if !o.Final {
		// Maintenance changes no ref, so a failure leaves the report
		// true, and the next sync tries again.
		if err := e.repo.Maintain(ctx); err != nil {
			slog.Warn("maintaining a copy failed", "repository", repo.Namespace+"/"+repo.Name, "err", err)
		}
	}
	return rep, nil
}

// Divergence returns how branch diverged between repo's copy and the
// external repository, or nil if it didn't. A branch diverges when each
// side changed it since they last agreed, and neither side's head keeps
// the other side's changes. Divergence shares each branch's last decision
// with Sync, so it doesn't compare heads that a sync compared, and returns
// the same error for heads that a sync couldn't compare.
func (m *Mirror) Divergence(ctx context.Context, repo *gitk8s.Repository, branch string) (*gitk8s.Divergence, error) {
	r, err := m.Open(ctx, repo)
	if err != nil {
		return nil, err
	}
	defer r.Close()
	refs, err := r.Refs(ctx, headsPrefix+branch, downstreamPrefix+branch, syncedPrefix+branch)
	if err != nil {
		return nil, err
	}
	head, down, synced := refs[headsPrefix+branch], refs[downstreamPrefix+branch], refs[syncedPrefix+branch]
	act, err := m.entry(repo).memo.decide(ctx, r.Repo, m.compareLimit(), branch, head, down, synced)
	if err != nil || act != diverged {
		return nil, err
	}
	d := &gitk8s.Divergence{Commit: down, Base: synced}
	if down != "" {
		d.Ref = downstreamPrefix + branch
	}
	return d, nil
}

func remoteOrError(f func() (git.Remote, error)) func() (git.Remote, error) {
	if f == nil {
		return func() (git.Remote, error) { return git.Remote{}, errors.New("mirror: SyncOptions.Remote is nil") }
	}
	return f
}

// action is what a sync does with one branch.
type action int

const (
	inSync action = iota
	// push sends the copy's head to the external repository.
	push
	// take moves the copy's head to the external repository's.
	take
	diverged
	// failed means that comparing the heads failed, so a sync leaves the
	// branch as it is on each side.
	failed
)

// decide says what to do with a branch whose head is m in the copy and d in
// the external repository, and that was s on both when they last agreed.
// "" means that the branch doesn't exist, or never agreed.
func decide(ctx context.Context, r *git.Repo, m, d, s string) (action, error) {
	switch {
	case m == d:
		return inSync, nil
	case d == s:
		return push, nil
	case m == s:
		return take, nil
	}
	if ok, err := r.Keeps(ctx, m, d, s); err != nil || ok {
		return push, err
	}
	if ok, err := r.Keeps(ctx, d, m, s); err != nil || ok {
		return take, err
	}
	return diverged, nil
}

// compareLimit returns the longest that deciding what to do with one
// branch may take.
func (m *Mirror) compareLimit() time.Duration {
	return cmp.Or(m.compareTimeout, 2*m.Git.MaxDuration())
}

// resolveSlow says how to resolve a branch whose heads took too long to
// compare.
const resolveSlow = "to resolve it, push the same commit to the branch in the mirror and in the external repository"

// memo remembers the last decision for each of a copy's branches.
type memo struct {
	mu   sync.Mutex
	last map[string]decision
}

// decision is what decide said about a branch whose heads were m, d, and
// s.
type decision struct {
	m, d, s string
	act     action
	err     error
}

// decide returns what to do with branch name, whose heads in r are m, d,
// and s, as the package's decide says, or failed and why if comparing the
// heads fails or takes longer than timeout. While the heads stay the same,
// it returns the branch's last decision again, even a comparison that took
// too long, so a branch that's slow to compare costs one comparison until a
// head moves or the process restarts. It doesn't remember another failure,
// such as a full disk, which can go away while the heads stay the same. If
// ctx ends first, decide returns the error and remembers nothing.
func (mo *memo) decide(ctx context.Context, r *git.Repo, timeout time.Duration, name, m, d, s string) (action, error) {
	mo.mu.Lock()
	last, ok := mo.last[name]
	mo.mu.Unlock()
	if ok && last.m == m && last.d == d && last.s == s {
		return last.act, last.err
	}
	dctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	act, err := decide(dctx, r, m, d, s)
	switch {
	case err == nil:
	case ctx.Err() != nil:
		return failed, err
	case dctx.Err() != nil:
		act, err = failed, fmt.Errorf("comparing the heads took longer than %v; %s", timeout, resolveSlow)
	case errors.Is(err, context.DeadlineExceeded):
		// One git command ran past git's own timeout.
		act, err = failed, fmt.Errorf("comparing the heads took too long: %w; %s", err, resolveSlow)
	default:
		return failed, err
	}
	mo.mu.Lock()
	defer mo.mu.Unlock()
	if mo.last == nil {
		mo.last = map[string]decision{}
	}
	mo.last[name] = decision{m: m, d: d, s: s, act: act, err: err}
	return act, err
}

// keep forgets the decisions about the branches that keep returns false
// for.
func (mo *memo) keep(keep func(name string) bool) {
	mo.mu.Lock()
	defer mo.mu.Unlock()
	maps.DeleteFunc(mo.last, func(name string, _ decision) bool { return !keep(name) })
}

// reset forgets every decision.
func (mo *memo) reset() {
	mo.mu.Lock()
	defer mo.mu.Unlock()
	mo.last = nil
}

type syncer struct {
	repo   *git.Repo
	remote func() (git.Remote, error)
	// memo is the copy's, and timeout limits each decision.
	memo    *memo
	timeout time.Duration
}

// branch is one branch's heads, as decide takes them, and what to do.
type branch struct {
	name    string
	m, d, s string
	act     action
	// err is why decide failed, if act is failed.
	err error
}

func (s *syncer) fetch(ctx context.Context) error {
	remote, err := s.remote()
	if err != nil {
		return err
	}
	if err := s.repo.FetchPrune(ctx, remote, "+refs/heads/*:"+downstreamPrefix+"*"); err != nil {
		return fmt.Errorf("fetching from the external repository: %w", err)
	}
	return nil
}

// plan reads every branch's heads and decides what to do with each. If
// deciding fails for a branch, such as when git times out on a long
// history, plan records the error on that branch, so one branch doesn't
// keep the others from syncing. plan forgets the decisions about branches
// that no longer exist.
func (s *syncer) plan(ctx context.Context) ([]branch, error) {
	refs, err := s.repo.Refs(ctx, "refs/heads", "refs/git-k8s/downstream/heads", "refs/git-k8s/synced/heads")
	if err != nil {
		return nil, err
	}
	byName := map[string]*branch{}
	for ref, sha := range refs {
		var name string
		var field func(*branch) *string
		switch {
		case strings.HasPrefix(ref, headsPrefix):
			name, field = ref[len(headsPrefix):], func(b *branch) *string { return &b.m }
		case strings.HasPrefix(ref, downstreamPrefix):
			name, field = ref[len(downstreamPrefix):], func(b *branch) *string { return &b.d }
		case strings.HasPrefix(ref, syncedPrefix):
			name, field = ref[len(syncedPrefix):], func(b *branch) *string { return &b.s }
		default:
			continue
		}
		// git could read such a name as an option, so the mirror neither
		// syncs nor lists the branch.
		if strings.HasPrefix(name, "-") {
			continue
		}
		b := byName[name]
		if b == nil {
			b = &branch{name: name}
			byName[name] = b
		}
		*field(b) = sha
	}
	var out []branch
	for _, name := range slices.Sorted(maps.Keys(byName)) {
		b := byName[name]
		b.act, b.err = s.memo.decide(ctx, s.repo, s.timeout, name, b.m, b.d, b.s)
		if b.err != nil && ctx.Err() != nil {
			return nil, b.err
		}
		out = append(out, *b)
	}
	s.memo.keep(func(name string) bool { return byName[name] != nil })
	return out, nil
}

// applyLocal takes the external repository's changes and records the
// branches that agree. It returns why it couldn't update each branch that
// it couldn't, as update does.
func (s *syncer) applyLocal(ctx context.Context, branches []branch) (map[string]error, error) {
	updates := map[string][]git.RefUpdate{}
	for _, b := range branches {
		switch {
		case b.act == take:
			updates[b.name] = []git.RefUpdate{
				{Ref: headsPrefix + b.name, New: b.d, Old: b.m},
				{Ref: syncedPrefix + b.name, New: b.d, Old: b.s},
			}
		case b.act == inSync && b.s != b.m:
			updates[b.name] = []git.RefUpdate{{Ref: syncedPrefix + b.name, New: b.m, Old: b.s}}
		}
	}
	return s.update(ctx, updates)
}

// push sends the copy's changes to the external repository, each with a
// lease on the external head that plan saw, and records the changes that
// the external repository took. It returns why the external repository
// refused each update that it refused, by ref, and why push couldn't
// record each branch that it couldn't, as update does.
func (s *syncer) push(ctx context.Context, branches []branch) (map[string]string, map[string]error, error) {
	var updates []git.RefUpdate
	for _, b := range branches {
		if b.act == push {
			updates = append(updates, git.RefUpdate{Ref: headsPrefix + b.name, New: b.m, Old: b.d})
		}
	}
	if len(updates) == 0 {
		return nil, nil, nil
	}
	remote, err := s.remote()
	if err != nil {
		return nil, nil, err
	}
	rejected, err := s.repo.PushEach(ctx, remote, updates...)
	if err != nil {
		return nil, nil, fmt.Errorf("pushing to the external repository: %w", err)
	}
	pushed := map[string][]git.RefUpdate{}
	for _, b := range branches {
		if _, no := rejected[headsPrefix+b.name]; b.act == push && !no {
			pushed[b.name] = []git.RefUpdate{
				{Ref: downstreamPrefix + b.name, New: b.m, Old: b.d},
				{Ref: syncedPrefix + b.name, New: b.m, Old: b.s},
			}
		}
	}
	unrecorded, err := s.update(ctx, pushed)
	return rejected, unrecorded, err
}

// update applies each branch's ref updates in the copy, which change
// together or not at all. It applies the branches whose updates delete
// refs before the others, because git refuses to delete refs/heads/a and
// create refs/heads/a/b in one transaction. The updates that a sync makes
// for one branch either all delete refs or none do. update tries the
// branches of each kind in one transaction, and then each branch alone if
// that fails. A branch whose updates fail because a push moved one of its
// refs since plan read it waits for the next sync, which looks at it
// again. update returns why the updates of each other branch failed, such
// as a lock that a killed git left, or a branch a in the copy when the
// updates create a/b. It returns an error only when ctx ends.
func (s *syncer) update(ctx context.Context, updates map[string][]git.RefUpdate) (map[string]error, error) {
	var deleting, other []string
	for _, name := range slices.Sorted(maps.Keys(updates)) {
		if slices.ContainsFunc(updates[name], func(u git.RefUpdate) bool { return u.New != "" }) {
			other = append(other, name)
		} else {
			deleting = append(deleting, name)
		}
	}
	failed := map[string]error{}
	for _, names := range [][]string{deleting, other} {
		var all []git.RefUpdate
		for _, name := range names {
			all = append(all, updates[name]...)
		}
		if len(all) == 0 {
			continue
		}
		err := s.repo.UpdateRefs(ctx, all...)
		if err == nil {
			continue
		}
		if ctx.Err() != nil {
			return nil, err
		}
		for _, name := range names {
			err := s.repo.UpdateRefs(ctx, updates[name]...)
			switch {
			case err == nil, errors.Is(err, git.ErrRejected):
			case ctx.Err() != nil:
				return nil, err
			default:
				failed[name] = err
			}
		}
	}
	return failed, nil
}

func refused(rejected map[string]string) error {
	var parts []string
	for _, ref := range slices.Sorted(maps.Keys(rejected)) {
		parts = append(parts, fmt.Sprintf("%s (%s)", strings.TrimPrefix(ref, headsPrefix), rejected[ref]))
	}
	return fmt.Errorf("the external repository refused updates to %s", strings.Join(parts, ", "))
}

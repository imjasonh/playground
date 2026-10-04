package mirror

import (
	"context"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strings"
	"sync"

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
	// Diverged maps each branch that changed both in the copy and in the
	// external repository since they last agreed to the external
	// repository's head.
	Diverged map[string]string
	// Err says why Sync couldn't fetch from or push to the external
	// repository.
	Err error
}

// Sync brings repo's copy and the external repository together, creating
// the copy if it doesn't exist. For each branch, it pushes a change made
// only in the copy, takes a change made only in the external repository,
// and leaves a branch that changed in both as it is on each side.
//
// Sync returns an error, and no report, when it has no branches to report:
// the copy hasn't fetched the external repository yet, and the error wraps
// ErrNotSynced, or local git failed. Failing to fetch from or push to the
// external repository after the copy has fetched once only sets the
// report's Err.
func (m *Mirror) Sync(ctx context.Context, repo *gitk8s.Repository, o SyncOptions) (*Report, error) {
	e := m.entry(repo)
	e.syncing.Lock()
	defer e.syncing.Unlock()
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

	s := &syncer{repo: e.repo, remote: sync.OnceValues(remoteOrError(o.Remote))}
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
		if err := s.applyLocal(ctx, branches); err != nil {
			return nil, err
		}
		if err := e.markSeeded(ctx); err != nil {
			return nil, err
		}
		if !o.Push {
			break
		}
		rejected, err := s.push(ctx, branches)
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
	rep.Heads, rep.Diverged = map[string]string{}, map[string]string{}
	for _, b := range branches {
		if b.m != "" {
			rep.Heads[b.name] = b.m
		}
		switch b.act {
		case push:
			rep.Pending = append(rep.Pending, b.name)
		case diverged:
			rep.Diverged[b.name] = b.d
		}
	}
	return rep, nil
}

// Divergence returns the external repository's head of branch if the
// branch changed both in repo's copy and in the external repository since
// they last agreed, or nil if it didn't.
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
	head, down := refs[headsPrefix+branch], refs[downstreamPrefix+branch]
	act, err := decide(ctx, r.Repo, head, down, refs[syncedPrefix+branch])
	if err != nil || act != diverged {
		return nil, err
	}
	return &gitk8s.Divergence{Commit: down, Ref: downstreamPrefix + branch}, nil
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
	case m == s || m == "":
		// A branch deleted in the copy and changed in the external
		// repository comes back, so that no commits are lost.
		return take, nil
	case d == "":
		return push, nil
	}
	// Both changed. If one side's head contains the other's, moving the
	// other side forward loses nothing; that's how a commit that resolves
	// a divergence syncs.
	if ok, err := r.IsAncestor(ctx, d, m); err != nil || ok {
		return push, err
	}
	if ok, err := r.IsAncestor(ctx, m, d); err != nil || ok {
		return take, err
	}
	return diverged, nil
}

type syncer struct {
	repo   *git.Repo
	remote func() (git.Remote, error)
}

// branch is one branch's heads, as decide takes them, and what to do.
type branch struct {
	name    string
	m, d, s string
	act     action
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

// plan reads every branch's heads and decides what to do with each.
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
		if b.act, err = decide(ctx, s.repo, b.m, b.d, b.s); err != nil {
			return nil, err
		}
		out = append(out, *b)
	}
	return out, nil
}

// applyLocal takes the external repository's changes and records the
// branches that agree.
func (s *syncer) applyLocal(ctx context.Context, branches []branch) error {
	var each [][]git.RefUpdate
	for _, b := range branches {
		switch {
		case b.act == take:
			each = append(each, []git.RefUpdate{
				{Ref: headsPrefix + b.name, New: b.d, Old: b.m},
				{Ref: syncedPrefix + b.name, New: b.d, Old: b.s},
			})
		case b.act == inSync && b.s != b.m:
			each = append(each, []git.RefUpdate{{Ref: syncedPrefix + b.name, New: b.m, Old: b.s}})
		}
	}
	if len(each) == 0 {
		return nil
	}
	err := s.repo.UpdateRefs(ctx, slices.Concat(each...)...)
	if !errors.Is(err, git.ErrRejected) {
		return err
	}
	// A push moved a branch since plan read it. Apply the other branches;
	// the next sync looks at that one again.
	for _, u := range each {
		if err := s.repo.UpdateRefs(ctx, u...); err != nil && !errors.Is(err, git.ErrRejected) {
			return err
		}
	}
	return nil
}

// push sends the copy's changes to the external repository, each with a
// lease on the external head that plan saw. It returns why the external
// repository refused each update that it refused, by ref.
func (s *syncer) push(ctx context.Context, branches []branch) (map[string]string, error) {
	var updates []git.RefUpdate
	for _, b := range branches {
		if b.act == push {
			updates = append(updates, git.RefUpdate{Ref: headsPrefix + b.name, New: b.m, Old: b.d})
		}
	}
	if len(updates) == 0 {
		return nil, nil
	}
	remote, err := s.remote()
	if err != nil {
		return nil, err
	}
	rejected, err := s.repo.PushEach(ctx, remote, updates...)
	if err != nil {
		return nil, fmt.Errorf("pushing to the external repository: %w", err)
	}
	var synced []git.RefUpdate
	for _, b := range branches {
		if _, no := rejected[headsPrefix+b.name]; b.act == push && !no {
			synced = append(synced,
				git.RefUpdate{Ref: downstreamPrefix + b.name, New: b.m, Old: b.d},
				git.RefUpdate{Ref: syncedPrefix + b.name, New: b.m, Old: b.s})
		}
	}
	if len(synced) > 0 {
		if err := s.repo.UpdateRefs(ctx, synced...); err != nil {
			return nil, err
		}
	}
	return rejected, nil
}

func refused(rejected map[string]string) error {
	var parts []string
	for _, ref := range slices.Sorted(maps.Keys(rejected)) {
		parts = append(parts, fmt.Sprintf("%s (%s)", strings.TrimPrefix(ref, headsPrefix), rejected[ref]))
	}
	return fmt.Errorf("the external repository refused updates to %s", strings.Join(parts, ", "))
}

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
	// Diverged maps each branch that diverged, as Mirror.Divergence says,
	// to the external repository's head, or to "" if the external
	// repository deleted the branch.
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

// Divergence returns how branch diverged between repo's copy and the
// external repository, or nil if it didn't. A branch diverges when each
// side changed it since they last agreed, and neither side's head keeps
// the other side's changes.
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
	act, err := decide(ctx, r.Repo, head, down, synced)
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
	if ok, err := keeps(ctx, r, m, d, s); err != nil || ok {
		return push, err
	}
	if ok, err := keeps(ctx, r, d, m, s); err != nil || ok {
		return take, err
	}
	return diverged, nil
}

// keeps reports whether moving one side of a branch from other to head
// keeps every change that side made since the sides agreed at s. The side
// removed the commits in s but not in other, and added the commits in
// other but not in s. head keeps them if:
//
//   - head has none of the removed commits;
//   - head has each added commit, or, if head doesn't contain s, a replay
//     of it, as Repo.Replays says; and
//   - if the side removed commits, or head doesn't contain other, head's
//     files have the side's changes, as keepsChanges and keepsRemoval say.
//
// The last check is what stops a rebased copy of a removed commit, which
// shares no commit with s, from bringing the removed change back. Replays
// alone aren't enough either, because two commits that make the same
// change on different lines have the same patch ID.
//
// head, other, and s differ, and "" means that the branch doesn't exist,
// or never agreed.
func keeps(ctx context.Context, r *git.Repo, head, other, s string) (bool, error) {
	switch {
	case s == "":
		return r.IsAncestor(ctx, other, head)
	case head == "":
		return r.IsAncestor(ctx, other, s)
	case other == "":
		bases, err := r.MergeBases(ctx, head, s)
		return len(bases) == 0, err
	}
	contains, err := r.IsAncestor(ctx, other, head)
	if err != nil {
		return false, err
	}
	if forward, err := r.IsAncestor(ctx, s, other); err != nil {
		return false, err
	} else if forward {
		if contains {
			return true, nil
		}
		// When both sides only added commits, replays would rewrite the
		// history of a side that didn't rewind.
		if ok, err := r.IsAncestor(ctx, s, head); err != nil || ok {
			return false, err
		}
		return keepsChanges(ctx, r, head, other, s)
	}
	// The commits that head and s share are their merge bases and the merge
	// bases' ancestors, so head has none of the commits that the side
	// removed if other contains each merge base.
	bases, err := r.MergeBases(ctx, head, s)
	if err != nil {
		return false, err
	}
	for _, b := range bases {
		if ok, err := r.IsAncestor(ctx, b, other); err != nil || !ok {
			return false, err
		}
	}
	if contains {
		return keepsRemoval(ctx, r, head, other, s)
	}
	return keepsChanges(ctx, r, head, other, s)
}

// keepsChanges reports whether head's files have every change from s's
// files to other's, and head has a replay of each commit that other added
// and head doesn't have. The file check runs first because it's cheap:
// Replays hashes commits that head has and other doesn't, which after a
// rebase can be all of main's new commits.
func keepsChanges(ctx context.Context, r *git.Repo, head, other, s string) (bool, error) {
	if ok, err := r.KeepsChanges(ctx, head, other, s); err != nil || !ok {
		return false, err
	}
	return r.Replays(ctx, head, other, s)
}

// keepsRemoval reports whether head, which contains other, keeps the
// changes of the commits that other's side removed since s out of its
// files. head has each commit that the side added, so it needs no
// replays. Either of two merges shows it, and each passes in a case where
// the other conflicts:
//
//   - Merging other into head, with s as the merge base, changes nothing.
//     This conflicts if head's own commits changed lines that the side
//     added, such as to resolve conflicts while replaying commits onto
//     other.
//   - Merging the commit where other and s meet, their only merge base,
//     changes nothing. This conflicts if the side's added commits changed
//     lines that the removed commits changed.
func keepsRemoval(ctx context.Context, r *git.Repo, head, other, s string) (bool, error) {
	if ok, err := r.KeepsChanges(ctx, head, other, s); err != nil || ok {
		return ok, err
	}
	bases, err := r.MergeBases(ctx, other, s)
	if err != nil || len(bases) != 1 || bases[0] == other {
		return false, err
	}
	return r.KeepsChanges(ctx, head, bases[0], s)
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

package mirror

import (
	"errors"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// world is a mirror that keeps a copy of one GitRepository, default/app.
type world struct {
	t *testing.T
	m *Mirror
	// work makes commits and pushes them.
	work *gittest.Work
	repo *gitk8s.Repository
	// remote is the external repository that Sync uses, and pushURL is
	// where the test pushes to it, with any credentials in the URL.
	remote  git.Remote
	pushURL string
	// remotes counts the calls of the Remote function that sync passes.
	remotes int

	// srv runs the mirror's handler, which finds served as the
	// GitRepository.
	srv    *httptest.Server
	mu     sync.Mutex
	served *gitk8s.GitRepository
}

// newWorld returns a world whose external repository is on a git server
// that needs a password.
func newWorld(t *testing.T) *world {
	t.Helper()
	ext := gittest.NewServer(t, "s3cret")
	u, err := url.Parse(ext.URL + "/app.git")
	if err != nil {
		t.Fatal(err)
	}
	u.User = url.UserPassword(ext.Username, ext.Password)
	return newWorldAt(t, ext.NewWork(t, "app"), ext.Remote("app"), u.String())
}

func newWorldAt(t *testing.T, work *gittest.Work, remote git.Remote, pushURL string) *world {
	repo := &gitk8s.Repository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: remote.URL}}
	repo.Namespace, repo.UID = "default", "uid-1"
	return &world{
		t:       t,
		m:       &Mirror{Git: &git.Git{}, Dir: t.TempDir()},
		work:    work,
		repo:    repo,
		remote:  remote,
		pushURL: pushURL,
	}
}

func (w *world) trySync(o SyncOptions) (*Report, error) {
	if o.Remote == nil {
		o.Remote = func() (git.Remote, error) {
			w.remotes++
			return w.remote, nil
		}
	}
	return w.m.Sync(w.t.Context(), w.repo, o)
}

func (w *world) sync(o SyncOptions) *Report {
	w.t.Helper()
	rep, err := w.trySync(o)
	if err != nil {
		w.t.Fatalf("Sync: %v", err)
	}
	return rep
}

// commit makes a commit whose parent is from, or that has no parent if
// from is "". The commit adds the file MESSAGE.txt, so commits with
// different messages make different changes.
func (w *world) commit(from, message string) string {
	w.t.Helper()
	if from == "" {
		w.work.Git("checkout", "--quiet", "--orphan", "orphan-"+message)
		w.work.Git("rm", "-r", "--quiet", "--force", "--ignore-unmatch", ".")
	} else {
		w.work.Git("checkout", "--quiet", "--detach", from)
	}
	w.work.Write(message+".txt", message+"\n")
	return w.work.Commit(message)
}

// replay replays commit onto onto, as git cherry-pick does, and returns the
// replay.
func (w *world) replay(commit, onto string) string {
	w.t.Helper()
	w.work.Git("checkout", "--quiet", "--detach", onto)
	w.work.Git("cherry-pick", "--allow-empty", commit)
	return w.work.Git("rev-parse", "HEAD")
}

// pushExternal sets branch to commit in the external repository, or
// deletes it if commit is "", as a person who pushes there does.
func (w *world) pushExternal(branch, commit string) {
	w.t.Helper()
	w.work.Git("push", "--quiet", "--force", w.pushURL, commit+":refs/heads/"+branch)
}

func (w *world) copyDir() string { return filepath.Join(w.m.Dir, "default", "app.git") }

// pushCopy sets branch to commit in the copy, or deletes it if commit is "",
// through the mirror's handler.
func (w *world) pushCopy(branch, commit string) {
	w.t.Helper()
	w.mirrorGit("push", "--quiet", "--force", w.serve(), commit+":refs/heads/"+branch)
}

// mirrorGit runs git with the token pusher, which belongs to a controller
// whose empty branch prefix lets it fetch, and push every branch.
func (w *world) mirrorGit(args ...string) string {
	w.t.Helper()
	return w.work.Git(append([]string{"-c", "http.extraHeader=Authorization: Bearer pusher"}, args...)...)
}

// serve returns the copy's URL on a server that runs the mirror's handler.
func (w *world) serve() string {
	w.t.Helper()
	w.mu.Lock()
	defer w.mu.Unlock()
	w.served = &gitk8s.GitRepository{Object: kube.Meta(w.repo.Name, nil), Spec: gitk8s.GitRepositorySpec{URL: w.repo.Spec.URL}}
	w.served.Namespace, w.served.UID = w.repo.Namespace, w.repo.UID
	if w.srv == nil {
		w.m.Prefixes = append(w.m.Prefixes, Prefix{Namespace: "test", ServiceAccount: "pusher"})
		token := kube.FakeToken{Token: "pusher", User: kube.UserInfo{Username: "system:serviceaccount:test:pusher"}, Audiences: []string{gitk8s.MirrorAudience}}
		w.srv = httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
			w.mu.Lock()
			repo := w.served
			w.mu.Unlock()
			ctx, rec := kube.FakeRequest(r.Context(), repo, token)
			w.m.ServeHTTP(rw, r.WithContext(ctx))
			if err := rec.Err(); err != nil {
				w.t.Errorf("the handler did what a kube.Serve handler can't: %v", err)
			}
		}))
		w.t.Cleanup(w.srv.Close)
	}
	return w.srv.URL + "/" + w.repo.Namespace + "/" + w.repo.Name + ".git"
}

// copyRefs lists the copy's refs under prefix, by name below prefix.
func (w *world) copyRefs(prefix string) map[string]string {
	w.t.Helper()
	out := w.work.Git("--git-dir="+w.copyDir(), "for-each-ref", "--format=%(refname) %(objectname)", prefix)
	refs := map[string]string{}
	for line := range strings.SplitSeq(out, "\n") {
		if ref, sha, ok := strings.Cut(line, " "); ok {
			refs[strings.TrimPrefix(ref, prefix)] = sha
		}
	}
	return refs
}

func (w *world) externalHeads() map[string]string {
	w.t.Helper()
	heads, err := w.m.Git.LsRemote(w.t.Context(), w.remote)
	if err != nil {
		w.t.Fatal(err)
	}
	return heads
}

func wantHeads(t *testing.T, what string, got, want map[string]string) {
	t.Helper()
	if !maps.Equal(got, want) {
		t.Errorf("%s = %v; want %v", what, got, want)
	}
}

func TestDecide(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	a := w.commit(base, "a")
	a2 := w.commit(a, "a2")
	b := w.commit(base, "b")
	// c adds a commit on a2. replayed is c replayed onto a, which drops
	// a2, and same is c replayed onto a2 under another message.
	c := w.commit(a2, "c")
	replayed := w.replay(c, a)
	w.work.Git("checkout", "--quiet", "--detach", a2)
	w.work.Git("cherry-pick", "-x", c)
	same := w.work.Git("rev-parse", "HEAD")
	other := w.commit(a, "other")
	r, err := w.m.Git.Open(t.Context(), filepath.Join(w.work.Dir, ".git"))
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name    string
		m, d, s string
		want    action
	}{
		{name: "the same on both sides", m: a, d: a, s: base, want: inSync},
		{name: "deleted on both sides", s: base, want: inSync},
		{name: "changed in the copy", m: a, d: base, s: base, want: push},
		{name: "created in the copy", m: a, want: push},
		{name: "deleted in the copy", d: base, s: base, want: push},
		{name: "rewound in the copy", m: a, d: a2, s: a2, want: push},
		{name: "changed in the external repository", m: base, d: a, s: base, want: take},
		{name: "created in the external repository", d: a, want: take},
		{name: "deleted in the external repository", m: base, s: base, want: take},
		{name: "rewound in the external repository", m: a2, d: a, s: a2, want: take},
		{name: "changed on both sides, the copy ahead", m: a2, d: a, s: base, want: push},
		{name: "changed on both sides, the external repository ahead", m: a, d: a2, s: base, want: take},
		{name: "changed on both sides", m: a, d: b, s: base, want: diverged},
		{name: "changed on both sides, with the same change", m: c, d: same, s: a2, want: diverged},
		{name: "created on both sides", m: a, d: b, want: diverged},
		{name: "created on both sides, the copy ahead", m: a2, d: a, want: push},
		{name: "deleted in the copy and changed in the external repository", d: a, s: base, want: diverged},
		{name: "changed in the copy and deleted in the external repository", m: a, s: base, want: diverged},
		{name: "deleted in the copy and rewound in the external repository", d: a, s: a2, want: push},
		{name: "rewound in the copy and deleted in the external repository", m: a, s: a2, want: take},
		{name: "rewound in the external repository and changed in the copy", m: c, d: a, s: a2, want: diverged},
		{name: "rewound in the copy and changed in the external repository", m: a, d: c, s: a2, want: diverged},
		{name: "rewound on both sides, the copy further", m: base, d: a, s: a2, want: push},
		{name: "rewound on both sides, the external repository further", m: a, d: base, s: a2, want: take},
		{name: "an external rewind, resolved in the copy", m: replayed, d: a, s: a2, want: push},
		{name: "an external rewind, resolved in the external repository", m: c, d: replayed, s: a2, want: take},
		{name: "a rewind in the copy, resolved in the copy", m: replayed, d: c, s: a2, want: push},
		{name: "a rewind in the copy, resolved in the external repository", m: a, d: replayed, s: a2, want: take},
		{name: "a rewind in the copy, resolved in the copy with another change", m: other, d: c, s: a2, want: diverged},
		{name: "a rewind in the copy, resolved in the external repository with another change", m: a, d: other, s: a2, want: take},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := decide(t.Context(), r, tc.m, tc.d, tc.s)
			if err != nil || got != tc.want {
				t.Errorf("decide = %v, %v; want %v", got, err, tc.want)
			}
		})
	}
}

func TestSyncFetchesNewCopy(t *testing.T) {
	w := newWorld(t)
	main := w.commit("", "first")
	w.pushExternal("main", main)
	w.pushExternal("release", main)

	if _, err := w.m.Open(t.Context(), w.repo); !errors.Is(err, ErrNotSynced) {
		t.Fatalf("Open before Sync = %v; want ErrNotSynced", err)
	}
	rep := w.sync(SyncOptions{})
	if !rep.Fetched || rep.Err != nil || len(rep.Pending) > 0 || len(rep.Diverged) > 0 {
		t.Errorf("Sync = %+v; want a fetch and nothing else", rep)
	}
	want := map[string]string{"main": main, "release": main}
	wantHeads(t, "Report.Heads", rep.Heads, want)
	wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), want)

	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatalf("Open after Sync: %v", err)
	}
	r.Close()

	// With nothing to fetch or push, Sync doesn't reach the external
	// repository.
	w.sync(SyncOptions{Push: true})
	if w.remotes != 1 {
		t.Errorf("Sync called Remote %d times; want 1", w.remotes)
	}

	// The copy survives a restart.
	restarted := &Mirror{Git: &git.Git{}, Dir: w.m.Dir}
	r, err = restarted.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatalf("Open after a restart: %v", err)
	}
	defer r.Close()
	heads, err := r.Refs(t.Context(), "refs/heads")
	if err != nil || heads["refs/heads/main"] != main {
		t.Errorf("after a restart, the copy has %v, %v; want main at %s", heads, err, main)
	}
}

func TestSyncPushesChangesMadeInCopy(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("old", base)
	w.sync(SyncOptions{})

	next := w.commit(base, "next")
	w.pushCopy("main", next)
	w.pushCopy("feature", next)
	w.pushCopy("old", "")

	rep := w.sync(SyncOptions{Fetch: true})
	if want := []string{"feature", "main", "old"}; !slices.Equal(rep.Pending, want) {
		t.Errorf("without Push, Report.Pending = %v; want %v", rep.Pending, want)
	}
	wantHeads(t, "Report.Heads", rep.Heads, map[string]string{"feature": next, "main": next})
	wantHeads(t, "without Push, the external repository's branches", w.externalHeads(), map[string]string{"main": base, "old": base})

	rep = w.sync(SyncOptions{Push: true})
	if len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("Sync = %+v; want nothing pending", rep)
	}
	want := map[string]string{"feature": next, "main": next}
	wantHeads(t, "the external repository's branches", w.externalHeads(), want)
	wantHeads(t, "the copy's downstream refs", w.copyRefs(downstreamPrefix), want)
	wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), want)
}

func TestSyncTakesChangesMadeInExternalRepository(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("old", base)
	w.sync(SyncOptions{})

	next := w.commit(base, "next")
	w.pushExternal("main", next)
	w.pushExternal("feature", next)
	w.pushExternal("old", "")

	rep := w.sync(SyncOptions{Push: true})
	wantHeads(t, "without a fetch, Report.Heads", rep.Heads, map[string]string{"main": base, "old": base})

	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	want := map[string]string{"feature": next, "main": next}
	wantHeads(t, "Report.Heads", rep.Heads, want)
	wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), want)
	wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), want)
	if len(rep.Pending) > 0 || len(rep.Diverged) > 0 || rep.Err != nil {
		t.Errorf("Sync = %+v; want nothing pending or diverged", rep)
	}
	if w.remotes != 2 {
		t.Errorf("Sync called Remote %d times; want 2, once for each fetch", w.remotes)
	}
}

func TestSyncRecordsDivergence(t *testing.T) {
	for _, resolve := range []string{"merge", "take the external head"} {
		t.Run(resolve, func(t *testing.T) {
			w := newWorld(t)
			base := w.commit("", "base")
			w.pushExternal("main", base)
			w.sync(SyncOptions{})

			ours := w.commit(base, "ours")
			theirs := w.commit(base, "theirs")
			w.pushCopy("main", ours)
			w.pushCopy("feature", ours)
			w.pushExternal("main", theirs)

			rep := w.sync(SyncOptions{Fetch: true, Push: true})
			wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"main": theirs})
			if len(rep.Pending) > 0 || rep.Err != nil {
				t.Errorf("Sync = %+v; want nothing pending", rep)
			}
			// Neither side's head moves, and other branches still sync.
			wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), map[string]string{"feature": ours, "main": ours})
			wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"feature": ours, "main": theirs})

			want := &gitk8s.Divergence{Commit: theirs, Ref: "refs/git-k8s/downstream/heads/main", Base: base}
			for _, m := range []*Mirror{w.m, {Git: &git.Git{}, Dir: w.m.Dir}} {
				d, err := m.Divergence(t.Context(), w.repo, "main")
				if err != nil || d == nil || *d != *want {
					t.Errorf("Divergence(main) = %+v, %v; want %+v", d, err, want)
				}
			}
			if d, err := w.m.Divergence(t.Context(), w.repo, "feature"); err != nil || d != nil {
				t.Errorf("Divergence(feature) = %+v, %v; want nil", d, err)
			}

			// Fetches see the external head and where the sides last
			// agreed.
			refs := w.mirrorGit("ls-remote", w.serve())
			if !strings.Contains(refs, theirs+"\trefs/git-k8s/downstream/heads/main") || !strings.Contains(refs, base+"\trefs/git-k8s/synced/heads/main") {
				t.Errorf("the mirror advertises\n%s\nwant downstream and synced refs", refs)
			}

			// A resolver fetches the external head from the mirror and
			// pushes a commit to the mirror that holds both heads, or the
			// external head itself.
			w.mirrorGit("fetch", "--quiet", w.serve(), want.Ref)
			resolved := theirs
			if resolve == "merge" {
				w.work.Git("checkout", "--quiet", "--detach", ours)
				w.work.Git("merge", "--quiet", "--no-edit", "FETCH_HEAD")
				resolved = w.work.Git("rev-parse", "HEAD")
			}
			w.pushCopy("main", resolved)

			rep = w.sync(SyncOptions{Push: true})
			if len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
				t.Errorf("after resolving, Sync = %+v; want nothing diverged or pending", rep)
			}
			wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"feature": ours, "main": resolved})
			if d, err := w.m.Divergence(t.Context(), w.repo, "main"); err != nil || d != nil {
				t.Errorf("after resolving, Divergence(main) = %+v, %v; want nil", d, err)
			}
		})
	}
}

// TestSyncKeepsRewinds has one side rewind feature to drop a commit, as a
// person does to remove a leaked secret, while the other side adds a commit
// on top of the dropped one. Moving either head to the other side would
// undo a change, even though one head contains the other, so the branch
// diverges until a replay of the added commit onto the rewound head
// resolves it, from either side.
func TestSyncKeepsRewinds(t *testing.T) {
	for _, tc := range []struct {
		name               string
		rewind, resolution string
	}{
		{name: "rewound in the external repository, resolved in the copy", rewind: "external", resolution: "copy"},
		{name: "rewound in the external repository, resolved there", rewind: "external", resolution: "external"},
		{name: "rewound in the copy, resolved there", rewind: "copy", resolution: "copy"},
		{name: "rewound in the copy, resolved in the external repository", rewind: "copy", resolution: "external"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := newWorld(t)
			a := w.commit("", "a")
			dropped := w.commit(a, "dropped")
			w.pushExternal("feature", dropped)
			w.sync(SyncOptions{})

			added := w.commit(dropped, "added")
			m, d := added, a
			if tc.rewind == "copy" {
				m, d = a, added
			}
			w.pushCopy("feature", m)
			w.pushExternal("feature", d)
			rep := w.sync(SyncOptions{Fetch: true, Push: true})
			wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"feature": d})
			wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), map[string]string{"feature": m})
			wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"feature": d})
			want := &gitk8s.Divergence{Commit: d, Ref: "refs/git-k8s/downstream/heads/feature", Base: dropped}
			if got, err := w.m.Divergence(t.Context(), w.repo, "feature"); err != nil || got == nil || *got != *want {
				t.Errorf("Divergence(feature) = %+v, %v; want %+v", got, err, want)
			}

			resolved := w.replay(added, a)
			if tc.resolution == "copy" {
				w.pushCopy("feature", resolved)
			} else {
				w.pushExternal("feature", resolved)
			}
			rep = w.sync(SyncOptions{Fetch: true, Push: true})
			if len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
				t.Errorf("after the replay, Sync = %+v; want nothing diverged or pending", rep)
			}
			want2 := map[string]string{"feature": resolved}
			wantHeads(t, "after the replay, the copy's branches", w.copyRefs("refs/heads/"), want2)
			wantHeads(t, "after the replay, the external repository's branches", w.externalHeads(), want2)
			wantHeads(t, "after the replay, the copy's synced refs", w.copyRefs(syncedPrefix), want2)
		})
	}
}

// TestSyncKeepsDeletions deletes a branch on one side while the other side
// changes it. A deletion removes every commit, so the branch diverges.
func TestSyncKeepsDeletions(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("ours", base)
	w.pushExternal("theirs", base)
	w.sync(SyncOptions{})

	next := w.commit(base, "next")
	w.pushCopy("ours", next)
	w.pushExternal("ours", "")
	w.pushCopy("theirs", "")
	w.pushExternal("theirs", next)
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"ours": "", "theirs": next})
	wantHeads(t, "Report.Heads", rep.Heads, map[string]string{"main": base, "ours": next})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"main": base, "theirs": next})
	if d, err := w.m.Divergence(t.Context(), w.repo, "ours"); err != nil || d == nil || *d != (gitk8s.Divergence{Base: base}) {
		t.Errorf("Divergence(ours) = %+v, %v; want only the base %s", d, err, base)
	}

	// Each side that kept the branch deletes it too.
	w.pushCopy("ours", "")
	w.pushExternal("theirs", "")
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("after the deletions, Sync = %+v; want nothing diverged or pending", rep)
	}
	wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), map[string]string{"main": base})
}

func TestSyncFetchesAgainWhenExternalRepositoryMoves(t *testing.T) {
	for _, tc := range []struct {
		name string
		// external is the commit that someone pushes to main in the
		// external repository after the mirror's last fetch, by name.
		external     string
		wantExternal string
		wantDiverged bool
	}{
		{name: "fast-forward", external: "a", wantExternal: "a2"},
		{name: "diverged", external: "b", wantExternal: "b", wantDiverged: true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := newWorld(t)
			base := w.commit("", "base")
			w.pushExternal("main", base)
			w.sync(SyncOptions{})

			commits := map[string]string{"a": w.commit(base, "a")}
			commits["a2"] = w.commit(commits["a"], "a2")
			commits["b"] = w.commit(base, "b")
			w.pushCopy("main", commits["a2"])
			w.pushExternal("main", commits[tc.external])

			// The push's lease on the external head fails, so Sync
			// fetches and looks again.
			rep := w.sync(SyncOptions{Push: true})
			if !rep.Fetched || rep.Err != nil || len(rep.Pending) > 0 {
				t.Errorf("Sync = %+v; want a fetch, and nothing pending", rep)
			}
			if got := len(rep.Diverged) > 0; got != tc.wantDiverged {
				t.Errorf("Report.Diverged = %v; want diverged %v", rep.Diverged, tc.wantDiverged)
			}
			wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"main": commits[tc.wantExternal]})
		})
	}
}

func TestSyncReportsRefusedPushes(t *testing.T) {
	ext := gittest.NewServer(t, "")
	w := newWorldAt(t, ext.NewWork(t, "app"), ext.Remote("app"), ext.Remote("app").URL)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("old", base)
	w.work.Git("--git-dir="+filepath.Join(ext.Root, "app.git"), "config", "receive.denyDeletes", "true")
	w.sync(SyncOptions{})

	w.pushCopy("old", "")
	w.pushCopy("feature", base)
	rep := w.sync(SyncOptions{Push: true})
	if rep.Err == nil || !strings.Contains(rep.Err.Error(), "refused updates to old") {
		t.Errorf("Report.Err = %v; want a refused update to old", rep.Err)
	}
	if want := []string{"old"}; !slices.Equal(rep.Pending, want) {
		t.Errorf("Report.Pending = %v; want %v", rep.Pending, want)
	}
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"feature": base, "main": base, "old": base})
}

func TestSyncWhenExternalRepositoryFails(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	errNoCredentials := errors.New("no credentials")
	noCredentials := func() (git.Remote, error) { return git.Remote{}, errNoCredentials }
	badPassword := func() (git.Remote, error) {
		return git.Remote{URL: w.remote.URL, Auth: &git.Auth{Username: "git-k8s", Password: "wrong"}}, nil
	}

	// Until the copy fetches once, Sync fails, and the mirror doesn't
	// serve the copy.
	if _, err := w.trySync(SyncOptions{Remote: noCredentials}); !errors.Is(err, ErrNotSynced) || !errors.Is(err, errNoCredentials) {
		t.Errorf("Sync without credentials = %v; want ErrNotSynced and the credentials error", err)
	}
	if _, err := w.trySync(SyncOptions{Remote: badPassword}); !errors.Is(err, ErrNotSynced) {
		t.Errorf("Sync with a bad password = %v; want ErrNotSynced", err)
	}
	if _, err := w.m.Open(t.Context(), w.repo); !errors.Is(err, ErrNotSynced) {
		t.Errorf("Open = %v; want ErrNotSynced", err)
	}

	// Afterward, Sync reports the copy's branches, and why it couldn't
	// reach the external repository.
	w.sync(SyncOptions{})
	w.pushCopy("feature", base)
	for name, remote := range map[string]func() (git.Remote, error){"no credentials": noCredentials, "a bad password": badPassword} {
		rep := w.sync(SyncOptions{Fetch: true, Push: true, Remote: remote})
		if rep.Err == nil || rep.Fetched {
			t.Errorf("with %s, Sync = %+v; want an error and no fetch", name, rep)
		}
		wantHeads(t, "Report.Heads", rep.Heads, map[string]string{"feature": base, "main": base})
		if want := []string{"feature"}; !slices.Equal(rep.Pending, want) {
			t.Errorf("with %s, Report.Pending = %v; want %v", name, rep.Pending, want)
		}
	}
	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatalf("Open = %v", err)
	}
	r.Close()
}

// A git that's killed while it updates a ref leaves the ref's lock file,
// which git never removes. Sync fails while a running git could hold the
// lock, and removes the lock once it's older than a git command can take.
func TestSyncRemovesStaleLocks(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	next := w.commit(base, "next")
	w.pushExternal("main", next)
	lock := filepath.Join(w.copyDir(), "refs", "heads", "main.lock")
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}

	for range 2 {
		if _, err := w.trySync(SyncOptions{Fetch: true}); err == nil || !strings.Contains(err.Error(), "main.lock") {
			t.Errorf("with a new lock, Sync = %v; want an error about the lock", err)
		}
	}
	if got := w.copyRefs("refs/heads/")["main"]; got != base {
		t.Errorf("with a new lock, the copy has main at %.7s, want %.7s", got, base)
	}

	old := time.Now().Add(-w.m.Git.MaxDuration() - 2*time.Minute)
	if err := os.Chtimes(lock, old, old); err != nil {
		t.Fatal(err)
	}
	if rep := w.sync(SyncOptions{Fetch: true}); rep.Heads["main"] != next {
		t.Errorf("with a stale lock, Report.Heads = %v; want main at the external head %.7s", rep.Heads, next)
	}
	if _, err := os.Stat(lock); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("the stale lock is still there: %v", err)
	}
}

// TestSyncRefusesLocalURLs points GitRepositories in another namespace at
// default/app's copy on the mirror's disk. Fetching from the copy would let
// that namespace read default/app, and pushing to it would skip the push
// rules.
func TestSyncRefusesLocalURLs(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	before := w.copyRefs("refs/")
	for _, url := range []string{w.copyDir(), "file://" + w.copyDir()} {
		thief := &gitk8s.Repository{Object: kube.Meta("thief", nil), Spec: gitk8s.GitRepositorySpec{URL: url}}
		thief.Namespace, thief.UID = "other", "uid-"+url
		_, err := w.m.Sync(t.Context(), thief, SyncOptions{Remote: func() (git.Remote, error) { return git.Remote{URL: url}, nil }})
		if !errors.Is(err, ErrNotSynced) || !strings.Contains(err.Error(), "not allowed") {
			t.Errorf("Sync from %s = %v; want ErrNotSynced, because git may not use the file transport", url, err)
		}
		if r, err := w.m.Open(t.Context(), thief); err == nil {
			r.Close()
			t.Errorf("Open of a copy of %s succeeded; want ErrNotSynced", url)
		} else if !errors.Is(err, ErrNotSynced) {
			t.Errorf("Open of a copy of %s = %v; want ErrNotSynced", url, err)
		}
	}
	wantHeads(t, "default/app's refs", w.copyRefs("refs/"), before)
}

// TestSyncSkipsBranchesThatLookLikeOptions has a branch whose name git
// could read as an option. A server accepts a push to it, though git branch
// refuses the name.
func TestSyncSkipsBranchesThatLookLikeOptions(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("-x", base)
	rep := w.sync(SyncOptions{})
	want := map[string]string{"main": base}
	wantHeads(t, "Report.Heads", rep.Heads, want)
	wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), want)
	if len(rep.Pending) > 0 || len(rep.Diverged) > 0 {
		t.Errorf("Sync = %+v; want nothing pending or diverged", rep)
	}
}

func TestSyncAdoptsNewURL(t *testing.T) {
	ext := gittest.NewServer(t, "")
	w := newWorldAt(t, ext.NewWork(t, "app"), ext.Remote("app"), ext.Remote("app").URL)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("old", base)
	w.sync(SyncOptions{})
	feature := w.commit(base, "feature")
	w.pushCopy("feature", feature)

	// The repository moves to a new URL, which has main but not the other
	// branches.
	w.pushURL = ext.Remote("moved").URL
	w.pushExternal("main", base)
	w.remote, w.repo.Spec.URL = ext.Remote("moved"), ext.Remote("moved").URL

	rep := w.sync(SyncOptions{Push: true})
	if !rep.Fetched || len(rep.Pending) > 0 || len(rep.Diverged) > 0 || rep.Err != nil {
		t.Errorf("Sync = %+v; want a fetch, and nothing pending or diverged", rep)
	}
	wantHeads(t, "the new external repository's branches", w.externalHeads(), map[string]string{"feature": feature, "main": base, "old": base})
}

func TestSyncReplacesCopyOfDeletedRepository(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	w.pushCopy("unsynced", w.commit(base, "unsynced"))

	// The GitRepository is deleted without its finalizer, and another with
	// the same name replaces it.
	old := *w.repo
	w.repo.UID = "uid-2"
	rep := w.sync(SyncOptions{Push: true})
	wantHeads(t, "Report.Heads", rep.Heads, map[string]string{"main": base})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"main": base})
	if _, err := w.m.Open(t.Context(), &old); !errors.Is(err, ErrNotSynced) {
		t.Errorf("Open of the deleted GitRepository = %v; want ErrNotSynced", err)
	}

	// Deleting the old GitRepository's copy leaves the new one's.
	if err := w.m.Delete(t.Context(), &old); err != nil {
		t.Fatal(err)
	}
	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatalf("Open after deleting the old copy: %v", err)
	}
	r.Close()

	if err := w.m.Delete(t.Context(), w.repo); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Dir(w.copyDir())); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("after Delete, the namespace's directory exists: %v", err)
	}
	if _, err := w.m.Open(t.Context(), w.repo); !errors.Is(err, ErrNotSynced) {
		t.Errorf("Open after Delete = %v; want ErrNotSynced", err)
	}
}

func TestSyncFinal(t *testing.T) {
	w := newWorld(t)
	rep := w.sync(SyncOptions{Final: true, Push: true})
	if rep.Heads != nil || w.remotes != 0 {
		t.Errorf("Sync with Final and no copy = %+v, after %d calls of Remote; want an empty report and none", rep, w.remotes)
	}
	if _, err := os.Stat(w.copyDir()); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("Sync with Final created a copy: %v", err)
	}

	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	w.pushCopy("feature", base)
	rep = w.sync(SyncOptions{Final: true, Push: true})
	if len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("Sync with Final = %+v; want nothing pending", rep)
	}
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"feature": base, "main": base})
}

func TestOpenWhileSyncing(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})

	var wg sync.WaitGroup
	for range 4 {
		wg.Go(func() {
			for range 5 {
				r, err := w.m.Open(t.Context(), w.repo)
				if err != nil {
					t.Error(err)
					return
				}
				if _, err := r.Refs(t.Context(), "refs/heads"); err != nil {
					t.Error(err)
				}
				r.Close()
			}
		})
	}
	for i := range 3 {
		w.pushExternal("main", w.commit(base, string(rune('a'+i))))
		w.sync(SyncOptions{Fetch: true, Push: true})
	}
	wg.Wait()
}

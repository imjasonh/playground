package mirror

import (
	"context"
	"errors"
	"fmt"
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

// commitFiles makes a commit whose parent is from, and that writes files,
// or deletes the ones whose content is "".
func (w *world) commitFiles(from, message string, files map[string]string) string {
	w.t.Helper()
	w.work.Git("checkout", "--quiet", "--detach", from)
	for path, content := range files {
		if content == "" {
			w.work.Git("rm", "--quiet", path)
		} else {
			w.work.Write(path, content)
		}
	}
	return w.work.Commit(message)
}

// reword makes a commit with commit's parent and files and another
// message.
func (w *world) reword(commit, message string) string {
	w.t.Helper()
	w.work.Git("checkout", "--quiet", "--detach", commit)
	w.work.Git("commit", "--quiet", "--amend", "--allow-empty", "-m", message)
	return w.work.Git("rev-parse", "HEAD")
}

// merge makes a merge commit whose parents are first and second.
func (w *world) merge(first, second string) string {
	w.t.Helper()
	w.work.Git("checkout", "--quiet", "--detach", first)
	w.work.Git("merge", "--quiet", "--no-ff", "--no-edit", second)
	return w.work.Git("rev-parse", "HEAD")
}

// numbered returns n lines, "line 1" to "line n", except that set replaces
// some of them.
func numbered(n int, set map[int]string) string {
	var b strings.Builder
	for i := 1; i <= n; i++ {
		line, ok := set[i]
		if !ok {
			line = fmt.Sprintf("line %d", i)
		}
		b.WriteString(line + "\n")
	}
	return b.String()
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
	// e and qux change a.txt in different ways on a. overridden merges qux
	// into e with -X theirs, so it contains e but has qux's a.txt.
	e := w.commitFiles(a, "e", map[string]string{"a.txt": "external\n"})
	qux := w.commitFiles(a, "qux", map[string]string{"a.txt": "qux\n"})
	w.work.Git("switch", "--quiet", "--detach", "--end-of-options", e)
	w.work.Git("merge", "--quiet", "--no-ff", "--no-edit", "-X", "theirs", "--end-of-options", qux)
	overridden := w.work.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
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
		{name: "an external rewind, merged in the copy with a change that overrides it", m: overridden, d: e, s: a2, want: diverged},
		{name: "a rewind in the copy, merged in the external repository with a change that overrides it", m: e, d: overridden, s: a2, want: diverged},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := decide(t.Context(), r, tc.m, tc.d, tc.s)
			if err != nil || got != tc.want {
				t.Errorf("decide = %v, %v; want %v", got, err, tc.want)
			}
		})
	}
}

// TestDecideRewrittenCommits covers heads that rebased, reworded, or
// replayed commits, so that what the commits changed, not which commits
// the heads share, decides whether a head keeps a side's changes.
func TestDecideRewrittenCommits(t *testing.T) {
	w := newWorld(t)
	file := func(set map[int]string) map[string]string { return map[string]string{"F": numbered(60, set)} }
	// F has "foo" on lines 10 and 50, so a commit that changes one of them
	// to "bar" has the same patch ID as one that changes the other.
	p := w.commitFiles(w.commit("", "root"), "p", file(map[int]string{10: "foo", 50: "foo"}))
	s := w.commit(p, "s")
	line10 := w.commitFiles(s, "line 10", file(map[int]string{10: "bar", 50: "foo"}))
	both := w.commitFiles(line10, "line 50 too", file(map[int]string{10: "bar", 50: "bar"}))
	line50NoS := w.commitFiles(p, "line 50 without s", file(map[int]string{10: "foo", 50: "bar"}))
	line10NoS := w.commitFiles(p, "line 10 without s", file(map[int]string{10: "bar", 50: "foo"}))
	// afterLine11 and afterLine12 replay the copy's change to line 10 in a
	// commit of its own, after a commit that changes line 11 or line 12.
	afterLine11 := w.commitFiles(w.commitFiles(p, "line 11 without s", file(map[int]string{10: "foo", 11: "eleven", 50: "foo"})),
		"line 10 after line 11", file(map[int]string{10: "bar", 11: "eleven", 50: "foo"}))
	afterLine12 := w.commitFiles(w.commitFiles(p, "line 12 without s", file(map[int]string{10: "foo", 12: "twelve", 50: "foo"})),
		"line 10 after line 12", file(map[int]string{10: "bar", 12: "twelve", 50: "foo"}))
	line50 := w.commitFiles(s, "line 50", file(map[int]string{10: "foo", 50: "bar"}))
	sOnLine10 := w.replay(s, line10NoS)
	// line10 then baz changes line 10 twice; onMain replays s and both
	// changes onto a newer main.
	baz := w.commitFiles(line10, "baz", file(map[int]string{10: "baz", 50: "foo"}))
	onMain := w.replay(baz, w.replay(line10, w.replay(s, w.commit(p, "main"))))

	// b is a commit that one side drops, as a person does to remove a
	// leaked secret.
	b := w.commit(p, "b")
	bRebased := w.replay(b, w.commit(p, "newer main"))
	bReworded := w.reword(b, "b, reworded")
	bMoved := w.reword(bRebased, "b, rebased and reworded")
	x := w.commit(b, "x")
	w.work.Git("checkout", "--quiet", "--detach", x)
	w.work.Git("revert", "--no-edit", x)
	reverted := w.work.Git("rev-parse", "HEAD")

	// After dropping secret, the external repository changes line 20,
	// which c, on secret, changed too. resolved replays c onto e, resolving
	// the conflict.
	secret := w.commit(p, "secret")
	c := w.commitFiles(secret, "c", file(map[int]string{10: "foo", 20: "copy", 50: "foo"}))
	e := w.commitFiles(p, "e", file(map[int]string{10: "foo", 20: "external", 50: "foo"}))
	resolved := w.commitFiles(e, "c, resolved", file(map[int]string{10: "foo", 20: "copy and external", 50: "foo"}))
	// merged merges e with next, which changes line 21, and keeps both
	// changes where git conflicts. mergedApart merges e with a commit that
	// changes line 22, which git merges cleanly.
	next := w.commitFiles(p, "line 21", file(map[int]string{10: "foo", 21: "copy", 50: "foo"}))
	kept := w.commitFiles(e, "lines 20 and 21", file(map[int]string{10: "foo", 20: "external", 21: "copy", 50: "foo"}))
	merged := w.work.Git("commit-tree", "-p", e, "-p", next, "-m", "merge line 21", "--end-of-options", kept+"^{tree}")
	mergedApart := w.merge(e, w.commitFiles(p, "line 22", file(map[int]string{10: "foo", 22: "copy", 50: "foo"})))
	// After dropping secretLine, which changed line 30, the external
	// repository changes line 30 another way. k, on secretLine, replays
	// onto that.
	secretLine := w.commitFiles(p, "secret line", file(map[int]string{10: "foo", 30: "secret", 50: "foo"}))
	scrubbed := w.commitFiles(p, "scrubbed", file(map[int]string{10: "foo", 30: "scrubbed", 50: "foo"}))
	kOnScrubbed := w.commit(scrubbed, "k")
	// A force push to e purges token and its revert, revoked, from one
	// side, as a person does to remove a leaked token from the history.
	// The other side made afterToken on revoked. rebased replays
	// afterToken onto e, and leaked replays token and revoked with it.
	// token and revoked undo each other, so leaked's tree doesn't have the
	// token, and only patch IDs tell leaked from rebased.
	token := w.commitFiles(p, "add a token", map[string]string{"t.txt": "token\n"})
	revoked := w.commitFiles(token, "remove the token", map[string]string{"t.txt": ""})
	afterToken := w.commit(revoked, "after the token")
	rebased := w.replay(afterToken, e)
	leaked := w.replay(afterToken, w.replay(revoked, w.replay(token, e)))

	bin1, bin2 := "\x00\x01\x02\x03\x04\x05\x00\xff", "\x00\x09\x09\x09\x04\x05\x00\xfe"
	q := w.commitFiles(p, "q", map[string]string{"A": "a content\n", "X.bin": bin1, "S.sh": "echo hi\n"})
	sq := w.commit(q, "sq")
	noSq := w.commit(q, "without sq")
	w.work.Git("checkout", "--quiet", "--detach", sq)
	empty := w.work.Commit("empty")
	emptyOnNewer := w.replay(empty, w.replay(sq, w.commit(q, "newest main")))
	executable := func(from string) string {
		w.work.Git("checkout", "--quiet", "--detach", from)
		if err := os.Chmod(filepath.Join(w.work.Dir, "S.sh"), 0o755); err != nil {
			t.Fatal(err)
		}
		return w.work.Commit("executable")
	}

	// x1 and x2 merged both ways are a criss-cross: m1 and m2 have two
	// merge bases.
	x1, x2 := w.commit(p, "x1"), w.commit(p, "x2")
	m1, m2 := w.merge(x1, x2), w.merge(x2, x1)

	r, err := w.m.Git.Open(t.Context(), filepath.Join(w.work.Dir, ".git"))
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name    string
		m, d, s string
		want    action
	}{
		{name: "the external repository rewound and replayed the copy's change", m: line10, d: line10NoS, s: s, want: take},
		// git conflicts on adjacent lines, so a replay of the copy's change
		// diverges if the external repository also changed the next line,
		// even though it keeps the copy's change.
		{name: "the external repository rewound, changed line 11, and replayed the copy's change to line 10", m: line10, d: afterLine11, s: s, want: diverged},
		{name: "the external repository rewound, changed line 12, and replayed the copy's change to line 10", m: line10, d: afterLine12, s: s, want: take},
		{name: "the external repository rewound and made the copy's change on another line", m: line10, d: line50NoS, s: s, want: diverged},
		{name: "the external repository rewound and made one of the copy's two changes", m: both, d: line10NoS, s: s, want: diverged},
		{name: "the copy rebased onto a main that made the external repository's change on another line", m: sOnLine10, d: line50, s: s, want: diverged},
		{name: "the copy rebased onto a newer main and replayed two changes to one line", m: onMain, d: baz, s: s, want: push},
		{name: "the external repository rebased onto a newer main and replayed two changes to one line", m: baz, d: onMain, s: s, want: take},

		{name: "the external repository dropped a commit, and the copy rebased it", m: bRebased, d: p, s: b, want: diverged},
		{name: "the copy dropped a commit, and the external repository rebased it", m: p, d: bRebased, s: b, want: diverged},
		{name: "the external repository dropped a commit, and the copy rebased and reworded it", m: bMoved, d: p, s: b, want: diverged},
		{name: "the external repository dropped a commit, and the copy reworded it", m: bReworded, d: p, s: b, want: diverged},
		{name: "the copy dropped a commit, and the external repository reworded it", m: p, d: bReworded, s: b, want: diverged},
		{name: "the external repository added a commit and its revert, and the copy rebased", m: bRebased, d: reverted, s: b, want: diverged},
		{name: "the copy added a commit and its revert, and the external repository rebased", m: reverted, d: bRebased, s: b, want: diverged},

		{name: "a rewind in the external repository, resolved in the copy with a conflict", m: resolved, d: e, s: secret, want: push},
		{name: "a rewind in the copy, resolved in the external repository with a conflict", m: e, d: resolved, s: secret, want: take},
		{name: "a rewind in the external repository, resolved in the copy with the dropped commit", m: w.replay(secret, resolved), d: e, s: secret, want: diverged},
		{name: "a rewind in the external repository, resolved there with a conflict", m: c, d: resolved, s: secret, want: diverged},
		{name: "a rewind in the external repository that rewrote the dropped line, resolved in the copy", m: kOnScrubbed, d: scrubbed, s: secretLine, want: push},
		// Neither merge is built on e, so merging e into it must be clean.
		{name: "a rewind in the external repository, merged in the copy with a change to the next line", m: merged, d: e, s: secret, want: diverged},
		{name: "a rewind in the copy, merged in the external repository with a change to the next line", m: e, d: merged, s: secret, want: diverged},
		{name: "a rewind in the external repository, merged in the copy with a change two lines away", m: mergedApart, d: e, s: secret, want: push},

		{name: "the external repository purged a token and its revert, and the copy rebased its commit", m: rebased, d: e, s: revoked, want: push},
		{name: "the copy purged a token and its revert, and the external repository rebased its commit", m: e, d: rebased, s: revoked, want: take},
		{name: "the external repository purged a token and its revert, and the copy rebased them with its commit", m: leaked, d: e, s: revoked, want: diverged},
		{name: "the copy purged a token and its revert, and the external repository rebased them with its commit", m: e, d: leaked, s: revoked, want: diverged},

		{name: "an empty commit in the copy, and the external repository rewound", m: empty, d: noSq, s: sq, want: diverged},
		{name: "an empty commit in the copy, replayed in the external repository", m: empty, d: emptyOnNewer, s: sq, want: diverged},
		{name: "a rename in the copy, replayed in the external repository", m: w.commitFiles(sq, "rename", map[string]string{"A": "", "B": "a content\n"}), d: w.commitFiles(noSq, "rename", map[string]string{"A": "", "B": "a content\n"}), s: sq, want: take},
		{name: "a binary change in the copy, replayed in the external repository", m: w.commitFiles(sq, "bin", map[string]string{"X.bin": bin2}), d: w.commitFiles(noSq, "bin", map[string]string{"X.bin": bin2}), s: sq, want: take},
		{name: "a binary change in the copy, and another in the external repository", m: w.commitFiles(sq, "bin", map[string]string{"X.bin": bin2}), d: w.commitFiles(noSq, "bin", map[string]string{"X.bin": bin2 + "x"}), s: sq, want: diverged},
		{name: "a mode change in the copy, replayed in the external repository", m: executable(sq), d: executable(noSq), s: sq, want: take},
		{name: "a mode change in the copy, and a content change in the external repository", m: executable(sq), d: w.commitFiles(noSq, "content", map[string]string{"S.sh": "echo bye\n"}), s: sq, want: diverged},
		{name: "a merge in the copy, and the external repository rewound", m: w.merge(w.commit(sq, "other"), w.commit(sq, "side")), d: noSq, s: sq, want: diverged},
		{name: "a rewind and a merge in the copy, and a commit in the external repository", m: w.merge(w.commit(q, "base 2"), w.commit(q, "side 2")), d: w.commit(sq, "ext"), s: sq, want: diverged},
		{name: "a commit in the copy, and the external repository recreated at an unrelated commit", m: w.commit(sq, "add"), d: w.commit("", "unrelated"), s: sq, want: diverged},
		{name: "a commit in the copy, and the external repository rebuilt the synced commit", m: w.commit(sq, "add"), d: w.reword(sq, "sq, rebuilt"), s: sq, want: diverged},

		{name: "a criss-cross merge in the copy, and the external repository replayed one side", m: m1, d: w.replay(x2, x1), s: m2, want: diverged},
		{name: "a criss-cross merge in the copy, and the external repository replayed the other side", m: m1, d: w.replay(x1, x2), s: m2, want: diverged},
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

// TestSyncResolvesRewindsWithConflicts follows the README's resolution of a
// rewind when the replay conflicts: after dropping a commit, one side
// changes a line that the other side's new commit changes too. Replaying
// that commit onto the rewound head, resolving the conflict, and pushing
// the result to the side that didn't rewind resolves the divergence.
func TestSyncResolvesRewindsWithConflicts(t *testing.T) {
	for _, rewind := range []string{"external repository", "copy"} {
		t.Run("rewound in the "+rewind, func(t *testing.T) {
			w := newWorld(t)
			lines := func(line20 string) map[string]string {
				return map[string]string{"F": numbered(30, map[int]string{20: line20})}
			}
			a := w.commitFiles(w.commit("", "a"), "F", lines("line 20"))
			dropped := w.commit(a, "dropped")
			w.pushExternal("feature", dropped)
			w.sync(SyncOptions{})

			added := w.commitFiles(dropped, "added", lines("added"))
			rewound := w.commitFiles(a, "rewound", lines("rewound"))
			m, d := added, rewound
			if rewind == "copy" {
				m, d = rewound, added
			}
			w.pushCopy("feature", m)
			w.pushExternal("feature", d)
			rep := w.sync(SyncOptions{Fetch: true, Push: true})
			wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"feature": d})

			resolved := w.commitFiles(rewound, "added, resolved", lines("added and rewound"))
			if rewind == "copy" {
				w.pushExternal("feature", resolved)
			} else {
				w.pushCopy("feature", resolved)
			}
			rep = w.sync(SyncOptions{Fetch: true, Push: true})
			if len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
				t.Errorf("after the resolution, Sync = %+v; want nothing diverged or pending", rep)
			}
			want := map[string]string{"feature": resolved}
			wantHeads(t, "after the resolution, the copy's branches", w.copyRefs("refs/heads/"), want)
			wantHeads(t, "after the resolution, the external repository's branches", w.externalHeads(), want)
		})
	}
}

// TestSyncKeepsAChangeOnAnotherLine has a person push a change to a
// dependency update's branch in the external repository while the copy
// rebases the update onto a main that made the same change on another
// line. The two changes have the same patch ID, but pushing the rebase
// would drop the person's change, so the branch diverges.
func TestSyncKeepsAChangeOnAnotherLine(t *testing.T) {
	w := newWorld(t)
	file := func(set map[int]string) map[string]string { return map[string]string{"F": numbered(60, set)} }
	m0 := w.commitFiles(w.commit("", "root"), "m0", file(map[int]string{10: "foo", 50: "foo"}))
	update := w.commit(m0, "update")
	w.pushExternal("main", m0)
	w.pushExternal("deps/x", update)
	w.sync(SyncOptions{})

	person := w.commitFiles(update, "person", file(map[int]string{10: "foo", 50: "bar"}))
	w.pushExternal("deps/x", person)
	m1 := w.commitFiles(m0, "m1", file(map[int]string{10: "bar", 50: "foo"}))
	w.pushCopy("deps/x", w.replay(update, m1))
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"deps/x": person})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"deps/x": person, "main": m0})
}

// TestSyncReportsABranchItCantCompare makes comparing one branch's heads
// fail, and checks that Sync reports the branch, leaves it as it is on
// each side, and still syncs the other branches.
func TestSyncReportsABranchItCantCompare(t *testing.T) {
	w := newWorld(t)
	main := w.commit("", "main")
	w.pushExternal("main", main)
	w.pushExternal("bad", main)
	w.sync(SyncOptions{})

	copyHead, extHead := w.commit(main, "copy"), w.commit(main, "external")
	w.pushCopy("bad", copyHead)
	w.pushExternal("bad", extHead)
	newer := w.commit(main, "newer")
	w.pushExternal("main", newer)
	// git merge-base fails on a synced head that isn't a commit.
	w.work.Git("--git-dir="+w.copyDir(), "update-ref", "refs/git-k8s/synced/heads/bad", main+"^{tree}")

	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	if err := rep.Failed["bad"]; len(rep.Failed) != 1 || err == nil || !strings.Contains(err.Error(), "merge-base") {
		t.Errorf("Report.Failed = %v; want bad, with git merge-base's error", rep.Failed)
	}
	if len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("Sync = %+v; want nothing diverged or pending", rep)
	}
	wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), map[string]string{"bad": copyHead, "main": newer})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"bad": extHead, "main": newer})
	if d, err := w.m.Divergence(t.Context(), w.repo, "bad"); err == nil {
		t.Errorf("Divergence = %+v; want an error, so the merge controller holds the branch", d)
	}
}

// TestSyncDecidesAgainOnlyWhenAHeadMoves gives comparisons a deadline that
// each one passes once a branch diverged, so deciding about the branch
// again fails, and checks that Sync and Divergence don't decide again until
// a head moves.
func TestSyncDecidesAgainOnlyWhenAHeadMoves(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("gone", base)
	w.sync(SyncOptions{})

	ours, theirs := w.commit(base, "ours"), w.commit(base, "theirs")
	w.pushCopy("main", ours)
	w.pushExternal("main", theirs)
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	wantHeads(t, "Report.Diverged", rep.Diverged, map[string]string{"main": theirs})

	w.m.compareTimeout = time.Nanosecond
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	wantHeads(t, "with the same heads, Report.Diverged", rep.Diverged, map[string]string{"main": theirs})
	if len(rep.Failed) > 0 {
		t.Errorf("with the same heads, Report.Failed = %v; want none", rep.Failed)
	}
	if d, err := w.m.Divergence(t.Context(), w.repo, "main"); err != nil || d == nil || d.Commit != theirs {
		t.Errorf("with the same heads, Divergence(main) = %+v, %v; want the external head", d, err)
	}

	// A person merges the copy's head in the external repository, which
	// moves the external head.
	merged := w.merge(theirs, ours)
	w.pushExternal("main", merged)
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if err := rep.Failed["main"]; err == nil || len(rep.Diverged) > 0 {
		t.Errorf("after the external head moved, Sync = %+v; want main failed, because deciding again passes the deadline", rep)
	}

	// With time to compare, a commit on top of the merge in the copy moves
	// the copy's head, and Sync pushes it.
	w.m.compareTimeout = 0
	top := w.commit(merged, "top")
	w.pushCopy("main", top)
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if len(rep.Failed) > 0 || len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("after the copy's head moved, Sync = %+v; want nothing failed, diverged, or pending", rep)
	}
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"gone": base, "main": top})

	// A branch that's gone from both sides leaves no decision behind.
	if _, ok := w.m.entry(w.repo).memo.last["gone"]; !ok {
		t.Fatal("the mirror has no decision about gone")
	}
	w.pushExternal("gone", "")
	w.pushCopy("gone", "")
	w.sync(SyncOptions{Fetch: true, Push: true})
	if _, ok := w.m.entry(w.repo).memo.last["gone"]; ok {
		t.Error("after both sides deleted gone, the mirror still has a decision about it")
	}
}

// TestSyncReportsAComparisonThatTakesTooLong gives comparisons a deadline
// that each one passes. Sync reports the branch as failed, with how to
// resolve it, and reports it again while the heads stay the same, even
// with time to compare them. A restart, or a head that moves, decides
// again.
func TestSyncReportsAComparisonThatTakesTooLong(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.pushExternal("other", base)
	w.sync(SyncOptions{})

	ours, theirs := w.commit(base, "ours"), w.commit(base, "theirs")
	w.pushCopy("main", ours)
	w.pushExternal("main", theirs)
	next := w.commit(base, "next")
	w.pushExternal("other", next)
	w.m.compareTimeout = time.Nanosecond
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	err := rep.Failed["main"]
	if len(rep.Failed) != 1 || err == nil || !strings.Contains(err.Error(), "took longer than 1ns") || !strings.Contains(err.Error(), "push the same commit to the branch in the mirror and in the external repository") {
		t.Fatalf("Report.Failed = %v; want main, for taking longer than 1ns, with how to resolve it", rep.Failed)
	}
	// A branch that needs no comparison still syncs.
	wantHeads(t, "the copy's branches", w.copyRefs("refs/heads/"), map[string]string{"main": ours, "other": next})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"main": theirs, "other": next})

	w.m.compareTimeout = 0
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if got := rep.Failed["main"]; got == nil || got.Error() != err.Error() || len(rep.Diverged) > 0 {
		t.Errorf("with time to compare the same heads, Sync = %+v; want main's failure again", rep)
	}
	if d, got := w.m.Divergence(t.Context(), w.repo, "main"); got == nil || got.Error() != err.Error() {
		t.Errorf("Divergence(main) = %+v, %v; want main's failure", d, got)
	}

	restarted := &Mirror{Git: &git.Git{}, Dir: w.m.Dir}
	if d, got := restarted.Divergence(t.Context(), w.repo, "main"); got != nil || d == nil || d.Commit != theirs {
		t.Errorf("after a restart, Divergence(main) = %+v, %v; want the external head", d, got)
	}

	// Pushing the external head to the copy puts the same commit on both
	// sides.
	w.pushCopy("main", theirs)
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if len(rep.Failed) > 0 || len(rep.Diverged) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("after pushing the external head to the copy, Sync = %+v; want nothing failed, diverged, or pending", rep)
	}
	wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), map[string]string{"main": theirs, "other": next})
}

// TestDecideForgetsACanceledComparison checks that a comparison that ends
// because its context ends, as when the process stops, isn't remembered.
func TestDecideForgetsACanceledComparison(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	ours, theirs := w.commit(base, "ours"), w.commit(base, "theirs")
	w.pushCopy("main", ours)
	w.pushExternal("main", theirs)
	w.sync(SyncOptions{Fetch: true})

	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	var mo memo
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	if act, err := mo.decide(ctx, r.Repo, time.Hour, "main", ours, theirs, base); err == nil {
		t.Fatalf("decide with a canceled context = %v; want an error", act)
	}
	if act, err := mo.decide(t.Context(), r.Repo, time.Hour, "main", ours, theirs, base); err != nil || act != diverged {
		t.Errorf("decide after a canceled one = %v, %v; want diverged", act, err)
	}
}

// TestPlanReturnsWhenItsContextEnds ends plan's context while git compares
// a branch's heads, as when the process stops, and checks that plan returns
// the error instead of reporting the branches as failed.
func TestPlanReturnsWhenItsContextEnds(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	w.pushCopy("main", w.commit(base, "ours"))
	w.pushExternal("main", w.commit(base, "theirs"))
	w.sync(SyncOptions{Fetch: true})

	// git merge-base, which comparing the heads runs, says that it started
	// and then waits.
	dir := t.TempDir()
	started := filepath.Join(dir, "started")
	bin := filepath.Join(dir, "git")
	script := "#!/bin/sh\ncase \" $* \" in\n*\" merge-base \"*) touch " + started + "; exec sleep 600 ;;\nesac\nexec git \"$@\"\n"
	if err := os.WriteFile(bin, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	w.m.Git.Bin = bin
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	go func() {
		for ctx.Err() == nil {
			if _, err := os.Stat(started); err == nil {
				cancel()
			}
			time.Sleep(10 * time.Millisecond)
		}
	}()
	s := &syncer{repo: r.Repo, memo: &memo{}, timeout: time.Hour}
	if branches, err := s.plan(ctx); !errors.Is(err, context.Canceled) || branches != nil {
		t.Errorf("plan = %+v, %v; want no branches and context.Canceled", branches, err)
	}
}

// scriptedGit makes w's git run through a script in a new directory, and
// returns the directory. While the directory has a file named fail, the
// script fails each git merge-base --is-ancestor as git does on an I/O
// error. While it has a file named hang, each one hangs.
func scriptedGit(t *testing.T, w *world) string {
	t.Helper()
	dir := t.TempDir()
	script := `#!/bin/sh
dir=$(dirname "$0")
for a in "$@"; do
	if [ "$a" = --is-ancestor ]; then
		if [ -e "$dir/fail" ]; then
			echo "fatal: simulated I/O error" >&2
			exit 128
		fi
		if [ -e "$dir/hang" ]; then
			exec sleep 600
		fi
	fi
done
exec git "$@"
`
	if err := os.WriteFile(filepath.Join(dir, "git"), []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	w.m.Git.Bin = filepath.Join(dir, "git")
	return dir
}

// TestSyncComparesAgainAfterAFailure fails a comparison as git does on an
// I/O error, then removes the cause without moving either head. Divergence
// and a final sync compare the heads again, so neither waits for a head to
// move or for a restart.
func TestSyncComparesAgainAfterAFailure(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})

	theirs := w.commit(base, "theirs")
	ours := w.commit(theirs, "ours")
	w.pushExternal("main", theirs)
	w.pushCopy("main", ours)
	fail := filepath.Join(scriptedGit(t, w), "fail")
	if err := os.WriteFile(fail, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	rep := w.sync(SyncOptions{Fetch: true})
	if err := rep.Failed["main"]; err == nil || !strings.Contains(err.Error(), "simulated I/O error") {
		t.Fatalf("while git fails, Report.Failed = %v; want main, with git's error", rep.Failed)
	}

	if err := os.Remove(fail); err != nil {
		t.Fatal(err)
	}
	if d, err := w.m.Divergence(t.Context(), w.repo, "main"); err != nil || d != nil {
		t.Errorf("after the fix, Divergence(main) = %+v, %v; want nil, nil", d, err)
	}
	rep = w.sync(SyncOptions{Push: true, Final: true})
	if len(rep.Failed) > 0 || len(rep.Pending) > 0 || rep.Err != nil {
		t.Errorf("after the fix, a final Sync = %+v; want main pushed", rep)
	}
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"main": ours})
}

// TestSyncReportsAGitCommandThatTakesTooLong makes one git command of a
// comparison run past git's timeout, which ends long before the
// comparison's deadline. Sync reports the branch as failed, with how to
// resolve it, and reports it again while the heads stay the same.
func TestSyncReportsAGitCommandThatTakesTooLong(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})

	ours, theirs := w.commit(base, "ours"), w.commit(base, "theirs")
	w.pushCopy("main", ours)
	w.pushExternal("main", theirs)
	hang := filepath.Join(scriptedGit(t, w), "hang")
	w.m.Git.Timeout = 3 * time.Second
	if err := os.WriteFile(hang, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	err := rep.Failed["main"]
	if err == nil || !errors.Is(err, context.DeadlineExceeded) || !strings.Contains(err.Error(), "push the same commit to the branch in the mirror and in the external repository") {
		t.Fatalf("Report.Failed = %v; want main, for git's timeout, with how to resolve it", rep.Failed)
	}

	if err := os.Remove(hang); err != nil {
		t.Fatal(err)
	}
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if got := rep.Failed["main"]; got == nil || got.Error() != err.Error() {
		t.Errorf("with the same heads, Report.Failed = %v; want main's failure again", rep.Failed)
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

// renames are branches that move to a name under their old one, and the
// reverse. git refuses to delete refs/heads/a and create refs/heads/a/b in
// one transaction, because refs/heads/a/ would be a directory where
// refs/heads/a is a file.
var renames = []struct{ name, from, to string }{
	{name: "nested", from: "a", to: "a/b"},
	{name: "unnested", from: "a/b", to: "a"},
}

func TestSyncTakesARenamedBranch(t *testing.T) {
	for _, tc := range renames {
		t.Run(tc.name, func(t *testing.T) {
			w := newWorld(t)
			base := w.commit("", "base")
			w.pushExternal("main", base)
			w.pushExternal(tc.from, base)
			w.sync(SyncOptions{})

			next, ours := w.commit(base, "next"), w.commit(base, "ours")
			w.pushExternal(tc.from, "")
			w.pushExternal(tc.to, next)
			w.pushCopy("main", ours)
			for i := range 2 {
				rep := w.sync(SyncOptions{Fetch: true, Push: true})
				if len(rep.Pending) > 0 || len(rep.Unapplied) > 0 || rep.Err != nil {
					t.Errorf("Sync %d = %+v; want nothing pending or unapplied", i+1, rep)
				}
			}
			want := map[string]string{"main": ours, tc.to: next}
			wantHeads(t, "the copy's branches", w.copyRefs(headsPrefix), want)
			wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), want)
			wantHeads(t, "the external repository's branches", w.externalHeads(), want)
		})
	}
}

func TestSyncPushesARenamedBranch(t *testing.T) {
	for _, tc := range renames {
		t.Run(tc.name, func(t *testing.T) {
			w := newWorld(t)
			base := w.commit("", "base")
			w.pushExternal("main", base)
			w.pushExternal(tc.from, base)
			w.sync(SyncOptions{})

			next := w.commit(base, "next")
			w.pushCopy(tc.from, "")
			w.pushCopy(tc.to, next)
			rep := w.sync(SyncOptions{Push: true})
			if len(rep.Pending) > 0 || len(rep.Unapplied) > 0 || rep.Err != nil {
				t.Errorf("Sync = %+v; want nothing pending or unapplied", rep)
			}
			want := map[string]string{"main": base, tc.to: next}
			wantHeads(t, "the external repository's branches", w.externalHeads(), want)
			wantHeads(t, "the copy's downstream refs", w.copyRefs(downstreamPrefix), want)
			wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), want)

			rep = w.sync(SyncOptions{Fetch: true, Push: true})
			if len(rep.Pending) > 0 || len(rep.Unapplied) > 0 || rep.Err != nil {
				t.Errorf("the next Sync = %+v; want nothing pending or unapplied", rep)
			}
		})
	}
}

// A final sync, which comes before the mirror deletes the copy, takes and
// pushes renamed branches too. Here a poll fetched the external
// repository's rename before the final sync.
func TestSyncFinalAfterRenames(t *testing.T) {
	for _, tc := range renames {
		t.Run(tc.name, func(t *testing.T) {
			w := newWorld(t)
			base := w.commit("", "base")
			theirs, ours := "theirs-"+tc.from, "ours-"+tc.from
			theirsTo, oursTo := "theirs-"+tc.to, "ours-"+tc.to
			w.pushExternal(theirs, base)
			w.pushExternal(ours, base)
			w.sync(SyncOptions{})

			next := w.commit(base, "next")
			w.pushExternal(theirs, "")
			w.pushExternal(theirsTo, next)
			w.work.Git("--git-dir="+w.copyDir(), "fetch", "--quiet", "--prune", w.pushURL, "+refs/heads/*:"+downstreamPrefix+"*")
			w.pushCopy(ours, "")
			w.pushCopy(oursTo, next)
			rep := w.sync(SyncOptions{Final: true, Push: true})
			if len(rep.Pending) > 0 || len(rep.Unapplied) > 0 || rep.Err != nil {
				t.Errorf("Sync with Final = %+v; want nothing pending or unapplied", rep)
			}
			want := map[string]string{theirsTo: next, oursTo: next}
			wantHeads(t, "the copy's branches", w.copyRefs(headsPrefix), want)
			wantHeads(t, "the external repository's branches", w.externalHeads(), want)
		})
	}
}

// When the copy has a branch a and the external repository a branch a/b,
// neither side can take the other's branch. Sync reports both, and still
// syncs the other branches.
func TestSyncReportsConflictingBranchNames(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})

	ours, theirs, next := w.commit(base, "ours"), w.commit(base, "theirs"), w.commit(base, "next")
	w.pushCopy("a", ours)
	w.pushExternal("a/b", theirs)
	w.pushCopy("main", next)
	rep := w.sync(SyncOptions{Fetch: true, Push: true})
	if len(rep.Unapplied) != 1 || rep.Unapplied["a/b"] == nil || !strings.Contains(rep.Unapplied["a/b"].Error(), "'refs/heads/a' exists") {
		t.Errorf("Report.Unapplied = %v; want a/b, because the copy has a", rep.Unapplied)
	}
	if want := []string{"a"}; !slices.Equal(rep.Pending, want) {
		t.Errorf("Report.Pending = %v; want %v", rep.Pending, want)
	}
	if rep.Err == nil || !strings.Contains(rep.Err.Error(), "refused updates to a (") {
		t.Errorf("Report.Err = %v; want the external repository's refusal of a", rep.Err)
	}
	wantHeads(t, "the copy's branches", w.copyRefs(headsPrefix), map[string]string{"a": ours, "main": next})
	wantHeads(t, "the external repository's branches", w.externalHeads(), map[string]string{"a/b": theirs, "main": next})

	// Once a person deletes a from the copy, a/b syncs.
	w.pushCopy("a", "")
	rep = w.sync(SyncOptions{Fetch: true, Push: true})
	if len(rep.Pending) > 0 || len(rep.Unapplied) > 0 || rep.Err != nil {
		t.Errorf("after the deletion, Sync = %+v; want nothing pending or unapplied", rep)
	}
	wantHeads(t, "the copy's branches", w.copyRefs(headsPrefix), map[string]string{"a/b": theirs, "main": next})
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
	if want := "the external repository refused updates to old ([remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/old)"; rep.Err == nil || rep.Err.Error() != want {
		t.Errorf("Report.Err = %v; want %q", rep.Err, want)
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
// which git never removes. Sync reports the branch while a running git
// could hold the lock, and removes the lock once it's older than a git
// command can take.
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
		rep := w.sync(SyncOptions{Fetch: true})
		if err := rep.Unapplied["main"]; err == nil || !strings.Contains(err.Error(), "main.lock") {
			t.Errorf("with a new lock, Report.Unapplied = %v; want main, with an error about the lock", rep.Unapplied)
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

// When a push moved a branch since plan read it, applyLocal applies each
// branch's updates alone, and leaves that branch for the next sync. It
// reports a branch whose updates fail for another reason, such as a lock
// that a killed git left.
func TestApplyLocalAfterAMovedBranch(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	next := w.commit(base, "next")
	w.pushExternal("main", next)
	w.sync(SyncOptions{})
	for _, name := range []string{"a", "b", "c"} {
		w.work.Git("--git-dir="+w.copyDir(), "update-ref", headsPrefix+name, base)
		w.work.Git("--git-dir="+w.copyDir(), "update-ref", syncedPrefix+name, base)
	}
	// A push moved a after plan read it, so the updates of every branch
	// at once fail. A killed git left c's lock.
	w.work.Git("--git-dir="+w.copyDir(), "update-ref", headsPrefix+"a", next)
	if err := os.WriteFile(filepath.Join(w.copyDir(), "refs", "heads", "c.lock"), nil, 0o644); err != nil {
		t.Fatal(err)
	}

	r, err := w.m.Open(t.Context(), w.repo)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	unapplied, err := (&syncer{repo: r.Repo}).applyLocal(t.Context(), []branch{
		{name: "a", act: take, m: base, d: next, s: base},
		{name: "b", act: take, m: base, d: next, s: base},
		{name: "c", act: take, m: base, d: next, s: base},
	})
	if err != nil {
		t.Fatalf("applyLocal: %v", err)
	}
	if len(unapplied) != 1 || unapplied["c"] == nil || !strings.Contains(unapplied["c"].Error(), "c.lock") {
		t.Errorf("applyLocal = %v; want only c, with an error about its lock", unapplied)
	}
	wantHeads(t, "the copy's branches", w.copyRefs(headsPrefix), map[string]string{"a": next, "b": next, "c": base, "main": next})
	wantHeads(t, "the copy's synced refs", w.copyRefs(syncedPrefix), map[string]string{"a": base, "b": next, "c": base, "main": next})
}

// A lock is stale once it's older than the longest that a git command can
// take, 5 minutes 10 seconds by default, plus a minute in case the volume's
// clock differs from the node's. Maintenance holds the locks under objects/
// for as long as it runs, so they're stale once they're older than the
// longest that maintenance can take, 1 hour 10 seconds by default, plus a
// minute. Sync keeps a newer lock, which a running git may hold, wherever
// it is in the copy.
func TestSyncRemovesOnlyStaleLocks(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})

	const stale, staleObjects = 6*time.Minute + 10*time.Second, time.Hour + time.Minute + 10*time.Second
	locks := map[string]time.Duration{
		"packed-refs.lock":        stale + time.Second,
		"HEAD.lock":               stale - time.Second,
		"refs/heads/feature.lock": stale + time.Second,
		"refs/heads/fix.lock":     stale - time.Second,
		"objects/info/commit-graphs/commit-graph-chain.lock": staleObjects + time.Second,
		"objects/maintenance.lock":                           staleObjects - time.Second,
	}
	now := time.Now()
	for path, age := range locks {
		path = filepath.Join(w.copyDir(), path)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, nil, 0o644); err != nil {
			t.Fatal(err)
		}
		if err := os.Chtimes(path, now.Add(-age), now.Add(-age)); err != nil {
			t.Fatal(err)
		}
	}

	w.sync(SyncOptions{})
	for path, age := range locks {
		cutoff := stale
		if strings.HasPrefix(path, "objects/") {
			cutoff = staleObjects
		}
		_, err := os.Stat(filepath.Join(w.copyDir(), path))
		if removed, want := errors.Is(err, os.ErrNotExist), age > cutoff; removed != want {
			t.Errorf("Sync removed %s, %v old: %t, want %t", path, age, removed, want)
		}
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

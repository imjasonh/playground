package main

import (
	"fmt"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// testTime is the committer time of gittest's commits, in git's raw format.
const testTime = "1767323045 +0000"

// landAs runs the merge controller on b, with a merge policy that lands
// branches with landing.
func landAs(t *testing.T, srv *gittest.Server, b *gitk8s.GitBranch, landing string) error {
	t.Helper()
	return landWith(t, srv, b, landing, git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}, nil)
}

// landWith is landAs with id as the merge controller's identity. If signer
// isn't nil, the GitRepository's signing Secret holds its key.
func landWith(t *testing.T, srv *gittest.Server, b *gitk8s.GitBranch, landing string, id git.Identity, signer *gittest.Signer) error {
	t.Helper()
	p := *b.Spec.Merge
	p.Landing = landing
	b.Spec.Merge = &p
	repo, secret := srv.Repository("app", rules()...)
	world := []any{repo, secret}
	if signer != nil {
		world = append(world, signer.Sign(repo))
	}
	ctx, _ := kube.Fake(t.Context(), b, world...)
	m := &merger{
		ident: id,
		cache: &gitk8s.Cache{Git: &git.Git{}, Dir: t.TempDir()},
	}
	return m.Reconcile(ctx, b)
}

// refresh pushes w's current commit to c/x and gives b fresh, passing results
// for it, like the repositories controller and the checks do.
func refresh(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
	t.Helper()
	w.Push("c/x")
	b.Spec.Head = w.Git("rev-parse", "HEAD")
	b.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed, FilesOnly: true},
		"gofmt": {Commit: b.Spec.Head, State: gitk8s.Passed, FilesOnly: true},
	}
}

// withHistoryCheck adds dco, a check whose passing result doesn't have
// filesOnly, such as one that reads commit messages, to b's merge policy.
func withHistoryCheck(b *gitk8s.GitBranch) {
	dco := gitk8s.CheckPolicy{Name: "dco"}
	if p := *b.Spec.Merge; !slices.Contains(p.Checks, dco) {
		p.Checks = append(p.Checks[:len(p.Checks):len(p.Checks)], dco)
		b.Spec.Merge = &p
	}
	b.Status.Checks["dco"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Passed}
}

// moveParent pushes a commit that writes a file to main, and leaves w on c/x.
func moveParent(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work, path, content string) {
	t.Helper()
	head := w.Git("rev-parse", "HEAD")
	w.Branch("main", b.Spec.ParentHead)
	w.Write(path, content)
	b.Spec.ParentHead = w.Commit("main moves")
	w.Push("main")
	w.Branch("c/x", head)
}

// mergeParent merges main into c/x, like check-base.
func mergeParent(b *gitk8s.GitBranch, w *gittest.Work) {
	w.Git("merge", "--quiet", "-m", "Merge main into c/x\n\nGit-K8s-Fixer: base", b.Spec.ParentHead)
}

// commitAsAna commits every change in the working tree as another author.
func commitAsAna(w *gittest.Work, message string) {
	w.Git("add", "-A")
	w.Git("commit", "--quiet", "--author=Ana Lima <ana@example.com>", "--date=1700000000 -0800", "-m", message)
}

// commitRaw commits the files in w's working tree with author and committer
// headers that git commit doesn't write, and leaves w on the commit.
func commitRaw(t *testing.T, w *gittest.Work, author, committer string) string {
	t.Helper()
	w.Git("add", "-A")
	raw := fmt.Sprintf("tree %s\nparent %s\nauthor %s\ncommitter %s\n\nadd y\n", w.Git("write-tree"), w.Git("rev-parse", "HEAD"), author, committer)
	path := filepath.Join(t.TempDir(), "commit")
	if err := os.WriteFile(path, []byte(raw), 0o644); err != nil {
		t.Fatal(err)
	}
	sha := w.Git("hash-object", "-t", "commit", "--literally", "-w", path)
	w.Git("reset", "--quiet", "--hard", sha)
	return sha
}

// commitMany adds n commits that change no files to w's current branch,
// with one git command.
func commitMany(t *testing.T, w *gittest.Work, n int) {
	t.Helper()
	var stream strings.Builder
	fmt.Fprintf(&stream, "reset refs/heads/many\nfrom %s\n\n", w.Git("rev-parse", "HEAD"))
	for i := range n {
		msg := fmt.Sprintf("commit %d\n", i)
		fmt.Fprintf(&stream, "commit refs/heads/many\ncommitter Test Author <author@example.com> %s\ndata %d\n%s\n", testTime, len(msg), msg)
	}
	cmd := exec.Command("git", "fast-import", "--quiet")
	cmd.Dir = w.Dir
	cmd.Stdin = strings.NewReader(stream.String())
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("git fast-import: %v\n%s", err, out)
	}
	w.Git("reset", "--quiet", "--hard", "many")
}

// commitBig adds a commit whose message has more than git.MaxLogBytes to
// w's current branch.
func commitBig(t *testing.T, w *gittest.Work) {
	t.Helper()
	path := filepath.Join(t.TempDir(), "message")
	if err := os.WriteFile(path, []byte("Big\n\n"+strings.Repeat("x", git.MaxLogBytes)+"\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	w.Git("commit", "--quiet", "--allow-empty", "-F", path)
}

// describeCommit returns a commit's parents, author, committer, and message.
func describeCommit(w *gittest.Work, sha string) string {
	return w.Git("log", "-1", "--date=raw", "--format=%P|%an <%ae> %ad|%cn <%ce> %cd|%B", sha)
}

func TestSquashLanding(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Write("y.txt", "y\n")
	commitAsAna(w, "Add y\n\nWith a body.\n\nSigned-off-by: Ana Lima <ana@example.com>")
	moveParent(t, b, w, "m.txt", "m\n")
	mergeParent(b, w)
	w.Write("x.txt", "x, formatted\n")
	w.Commit("Format Go files with gofmt\n\nGit-K8s-Fixer: gofmt")
	refresh(t, b, w)
	main := b.Spec.ParentHead
	if err := landAs(t, srv, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	if _, ok := srv.Heads(t, "app")["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	squashed := w.Fetch("main")
	want := strings.Join([]string{
		main,
		"Test Author <author@example.com> " + testTime,
		"git-k8s <git-k8s@example.com> " + testTime,
		"add x\n\n* add x\n* Add y\n* Format Go files with gofmt\n\nSigned-off-by: Ana Lima <ana@example.com>\nCo-authored-by: Ana Lima <ana@example.com>",
	}, "|")
	if got := describeCommit(w, squashed); got != want {
		t.Errorf("squashed commit:\n%s\nwant:\n%s", got, want)
	}
	if got, want := w.Git("rev-parse", squashed+"^{tree}"), w.Git("rev-parse", b.Spec.Head+"^{tree}"); got != want {
		t.Errorf("squashed tree = %s, want the head's tree %s", got, want)
	}
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	msg := fmt.Sprintf("squashed c/x onto main, which moved from %s to %s", gitk8s.Short(main), gitk8s.Short(squashed))
	if c == nil || c.Status != kube.True || c.Message != msg || b.Status.State != reasonLanded {
		t.Errorf("Merged = %+v, state %q", c, b.Status.State)
	}
}

func TestSquashMessage(t *testing.T) {
	ana := git.Signature{Name: "Ana Lima", Email: "ana@example.com", Date: "1700000000 -0800"}
	bo := git.Signature{Name: "Bo Chen", Email: "bo@example.com", Date: "1700000100 +0000"}
	anaSigned := "Signed-off-by: Ana Lima <ana@example.com>"
	fix := git.LogEntry{Parents: []string{"p"}, Author: bo, Message: "Format Go files with gofmt\n\nGit-K8s-Fixer: gofmt\n", Trailers: []string{"Git-K8s-Fixer: gofmt"}}
	merge := git.LogEntry{Parents: []string{"p", "q"}, Author: bo, Message: "Merge main into c/x\n\nGit-K8s-Fixer: base\n", Trailers: []string{"Git-K8s-Fixer: base"}}
	for _, tt := range []struct {
		name    string
		log     []git.LogEntry
		author  git.Signature
		message string
	}{{
		name:    "one person's commit",
		log:     []git.LogEntry{{Parents: []string{"p"}, Author: ana, Message: "Add y\n\nWith a body.\n"}, merge, fix},
		author:  ana,
		message: "Add y\n\nWith a body.\n",
	}, {
		name: "several commits",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\n" + anaSigned + "\n", Trailers: []string{anaSigned}},
			{
				Parents:  []string{"p"},
				Author:   bo,
				Message:  "Add z\n\nWith a body.\n\nCo-authored-by: Cy Diaz <cy@example.com>\nFixes: #12\n",
				Trailers: []string{"Co-authored-by: Cy Diaz <cy@example.com>", "Fixes: #12"},
			},
			merge,
			{Parents: []string{"p"}, Author: git.Signature{Name: "Ana", Email: "ANA@example.com"}, Message: "Fix y\n\n" + anaSigned + "\n", Trailers: []string{anaSigned}},
			fix,
		},
		author: ana,
		message: "Add y\n\n* Add y\n* Add z\n* Fix y\n* Format Go files with gofmt\n\n" +
			anaSigned + "\nCo-authored-by: Cy Diaz <cy@example.com>\nFixes: #12\nCo-authored-by: Bo Chen <bo@example.com>\n",
	}, {
		name:    "only a fix",
		log:     []git.LogEntry{merge, fix},
		author:  bo,
		message: "Format Go files with gofmt\n",
	}, {
		name: "only fixes",
		log: []git.LogEntry{fix, {
			Parents:  []string{"p"},
			Author:   ana,
			Message:  "Add license headers\n\nGit-K8s-Fixer: license\n",
			Trailers: []string{"Git-K8s-Fixer: license"},
		}},
		author:  bo,
		message: "Format Go files with gofmt\n\n* Format Go files with gofmt\n* Add license headers\n\nCo-authored-by: Ana Lima <ana@example.com>\n",
	}, {
		// git reads "Git-K8s-Fixer : x" and "git-k8s-fixer: y" as the
		// fixer trailer, though the commits don't count as fixes.
		name:    "one person's commit with a trailer like the fixer trailer",
		log:     []git.LogEntry{{Parents: []string{"p"}, Author: ana, Message: "Add y\n\nGit-K8s-Fixer : x\n" + anaSigned + "\n"}, fix},
		author:  ana,
		message: "Add y\n\n" + anaSigned + "\n",
	}, {
		name: "several commits with trailers like the fixer trailer",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\nGit-K8s-Fixer : x\n", Trailers: []string{"Git-K8s-Fixer: x"}},
			{Parents: []string{"p"}, Author: bo, Message: "Add z\n\ngit-k8s-fixer: y\n" + anaSigned + "\n", Trailers: []string{"git-k8s-fixer: y", anaSigned}},
		},
		author:  ana,
		message: "Add y\n\n* Add y\n* Add z\n\n" + anaSigned + "\nCo-authored-by: Bo Chen <bo@example.com>\n",
	}, {
		name:    "only a merge",
		log:     []git.LogEntry{{Parents: []string{"p", "q"}, Author: ana, Message: "Merge feature\n"}},
		author:  ana,
		message: "Merge feature\n",
	}} {
		t.Run(tt.name, func(t *testing.T) {
			from, message := squashMessage(tt.log)
			if from.Author != tt.author || message != tt.message {
				t.Errorf("squashMessage = %+v, %q; want %+v, %q", from.Author, message, tt.author, tt.message)
			}
		})
	}
}

func TestRebaseLanding(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Write("y.txt", "y\n")
	commitAsAna(w, "Add y\n\nWith a body.")
	moveParent(t, b, w, "m.txt", "m\n")
	mergeParent(b, w)
	w.Write("z.txt", "z\n")
	w.Commit("add z")
	refresh(t, b, w)
	main := b.Spec.ParentHead
	if err := landAs(t, srv, b, gitk8s.Rebase); err != nil {
		t.Fatal(err)
	}
	if _, ok := srv.Heads(t, "app")["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	rebased := w.Fetch("main")
	if got, want := w.Git("rev-parse", rebased+"^{tree}"), w.Git("rev-parse", b.Spec.Head+"^{tree}"); got != want {
		t.Errorf("rebased tree = %s, want the head's tree %s", got, want)
	}
	committer := "|git-k8s <git-k8s@example.com> " + testTime + "|"
	want := []string{
		"Test Author <author@example.com> " + testTime + committer + "add x",
		"Ana Lima <ana@example.com> 1700000000 -0800" + committer + "Add y\n\nWith a body.",
		"Test Author <author@example.com> " + testTime + committer + "add z",
	}
	commits := strings.Fields(w.Git("rev-list", "--reverse", main+".."+rebased))
	if len(commits) != len(want) {
		t.Fatalf("main has %d new commits, want %d: %s", len(commits), len(want), w.Git("log", "--oneline", main+".."+rebased))
	}
	parent := main
	for i, c := range commits {
		if got := describeCommit(w, c); got != parent+"|"+want[i] {
			t.Errorf("rebased commit %d:\n%s\nwant:\n%s", i, got, parent+"|"+want[i])
		}
		parent = c
	}
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	msg := fmt.Sprintf("rebased c/x onto main, which moved from %s to %s", gitk8s.Short(main), gitk8s.Short(rebased))
	if c == nil || c.Status != kube.True || c.Message != msg || b.Status.State != reasonLanded {
		t.Errorf("Merged = %+v, state %q", c, b.Status.State)
	}
}

// Squash and rebase landings sign the commits that they make with the
// GitRepository's key, including a squashed commit that the merge
// controller pushes to the branch for the checks.
func TestLandingsSign(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	id := git.Identity{Name: "git-k8s", Email: signer.Email}
	for _, tt := range []struct {
		name, landing string
		history       bool
		ref           string
		commits       int
	}{
		{"squash", gitk8s.Squash, false, "main", 1},
		{"rebase", gitk8s.Rebase, false, "main", 2},
		{"squash for the checks", gitk8s.Squash, true, "c/x", 1},
	} {
		t.Run(tt.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			w.Write("y.txt", "y\n")
			commitAsAna(w, "Add y")
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, b, w)
			if tt.history {
				withHistoryCheck(b)
			}
			main := b.Spec.ParentHead
			if err := landWith(t, srv, b, tt.landing, id, signer); err != nil {
				t.Fatal(err)
			}
			commits := strings.Fields(w.Git("rev-list", main+".."+w.Fetch(tt.ref)))
			if len(commits) != tt.commits {
				t.Fatalf("%s has %d commits that main didn't, want %d", tt.ref, len(commits), tt.commits)
			}
			for _, c := range commits {
				if err := signer.Verify(w.Dir, c); err != nil {
					t.Error(err)
				}
			}
		})
	}
}

// A landing that can't read the signing key pushes nothing, but a landing
// that makes no commits doesn't read the key.
func TestLandingNeedsTheSigningKey(t *testing.T) {
	broken := &gittest.Signer{Email: "git-k8s@example.com", Key: []byte("hunter2")}
	id := git.Identity{Name: "git-k8s", Email: broken.Email}
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, b, w)
			before := srv.Heads(t, "app")
			err := landWith(t, srv, b, landing, id, broken)
			if err == nil || !strings.Contains(err.Error(), "reading the signing key: Secret app-signing: the key isn't a private key") || strings.Contains(err.Error(), "hunter2") {
				t.Fatalf("err = %v, want one that says the signing key isn't a key, without the Secret's data", err)
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}

			moveParent(t, b, w, "x.txt", "x\n")
			mergeParent(b, w)
			refresh(t, b, w)
			if err := landWith(t, srv, b, landing, id, broken); err != nil || b.Status.State != reasonMerged {
				t.Errorf("landing a branch whose changes the parent has: state %q, %v; want %s", b.Status.State, err, reasonMerged)
			}
		})
	}
}

// A rebase landing leaves out a commit whose change the parent already has.
func TestRebaseLeavesOutChangesInTheParent(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Write("y.txt", "y\n")
	w.Commit("add y")
	moveParent(t, b, w, "y.txt", "y\n")
	mergeParent(b, w)
	refresh(t, b, w)
	main := b.Spec.ParentHead
	if err := landAs(t, srv, b, gitk8s.Rebase); err != nil {
		t.Fatal(err)
	}
	rebased := w.Fetch("main")
	if got := w.Git("log", "--format=%s", main+".."+rebased); got != "add x" {
		t.Errorf("main's new commits = %q, want only add x", got)
	}
	if got, want := w.Git("rev-parse", rebased+"^{tree}"), w.Git("rev-parse", b.Spec.Head+"^{tree}"); got != want {
		t.Errorf("rebased tree = %s, want the head's tree %s", got, want)
	}
}

// A branch that a squash or rebase landing leaves as it is lands by
// fast-forward, which keeps its commits.
func TestRewriteFastForwards(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			if landing == gitk8s.Rebase {
				w.Write("y.txt", "y\n")
				w.Commit("add y")
				refresh(t, b, w)
			}
			main, head := b.Spec.ParentHead, b.Spec.Head
			if err := landAs(t, srv, b, landing); err != nil {
				t.Fatal(err)
			}
			heads := srv.Heads(t, "app")
			if heads["main"] != head {
				t.Errorf("main = %s, want %s", heads["main"], head)
			}
			if _, ok := heads["c/x"]; ok {
				t.Error("c/x wasn't deleted after it landed")
			}
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			msg := fmt.Sprintf("fast-forwarded main from %s to %s", gitk8s.Short(main), gitk8s.Short(head))
			if c == nil || c.Reason != reasonLanded || c.Message != msg {
				t.Errorf("Merged = %+v", c)
			}
		})
	}
}

// Without deleteMergedBranches, the branch moves to the landed commit in the
// same push, so it stays in its parent.
func TestRewriteMovesAKeptBranch(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, b, w)
			p := *b.Spec.Merge
			p.DeleteMergedBranches = false
			b.Spec.Merge = &p
			main := b.Spec.ParentHead
			if err := landAs(t, srv, b, landing); err != nil {
				t.Fatal(err)
			}
			heads := srv.Heads(t, "app")
			if heads["main"] == main || heads["main"] == b.Spec.Head || heads["c/x"] != heads["main"] {
				t.Errorf("main = %s, c/x = %s; want both at a new commit on %s", heads["main"], heads["c/x"], main)
			}
			if b.Status.State != reasonLanded {
				t.Errorf("state = %q, want %s", b.Status.State, reasonLanded)
			}
		})
	}
}

// A branch whose changes the parent already has leaves the parent as it is.
func TestRewriteWithNothingToLand(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			moveParent(t, b, w, "x.txt", "x\n")
			mergeParent(b, w)
			refresh(t, b, w)
			before := srv.Heads(t, "app")
			if err := landAs(t, srv, b, landing); err != nil {
				t.Fatal(err)
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			if c == nil || c.Status != kube.True || b.Status.State != reasonMerged {
				t.Errorf("Merged = %+v, state %q", c, b.Status.State)
			}
		})
	}
}

// A branch that a rebase can't copy needs a person, but a squash landing
// lands it, because it only needs the head's files.
func TestRebaseNeedsRebase(t *testing.T) {
	for name, tt := range map[string]struct {
		setup   func(*testing.T, *gitk8s.GitBranch, *gittest.Work)
		problem string
	}{
		"conflict resolved in a merge": {
			setup: func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
				moveParent(t, b, w, "x.txt", "main\n")
				w.Git("merge", "--quiet", "--no-commit", "-s", "ours", b.Spec.ParentHead)
				w.Write("x.txt", "x\nmain\n")
				w.Commit("Merge main into c/x")
			},
			problem: "conflicts in x.txt",
		},
		"merge that changes files": {
			setup: func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
				moveParent(t, b, w, "m.txt", "m\n")
				w.Git("merge", "--quiet", "--no-commit", "--no-ff", b.Spec.ParentHead)
				w.Write("e.txt", "e\n")
				w.Commit("Merge main into c/x")
			},
			problem: "because merge commits in the branch change files, and a rebase leaves merges out",
		},
		"unrelated history": {
			setup: func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
				root := w.Git("commit-tree", "4b825dc642cb6eb9a060e54bf8d69288fbee4904", "-m", "unrelated")
				w.Git("merge", "--quiet", "--allow-unrelated-histories", "-m", "Merge unrelated", root)
			},
			problem: "has no parent",
		},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			tt.setup(t, b, w)
			refresh(t, b, w)
			results := b.Status.Checks
			before := srv.Heads(t, "app")
			if err := landAs(t, srv, b, gitk8s.Rebase); err != nil {
				t.Fatal(err)
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			if c == nil || c.Status != kube.False || c.Reason != reasonNeedsRebase || !strings.Contains(c.Message, tt.problem) {
				t.Errorf("Merged = %+v, want reason %s and a message with %q", c, reasonNeedsRebase, tt.problem)
			}

			b.Status.Checks = results
			if err := landAs(t, srv, b, gitk8s.Squash); err != nil {
				t.Fatal(err)
			}
			squashed := w.Fetch("main")
			if got, want := w.Git("rev-parse", squashed+"^{tree}"), w.Git("rev-parse", b.Spec.Head+"^{tree}"); got != want || b.Status.State != reasonLanded {
				t.Errorf("after a squash landing, state = %q and main's tree = %s, want %s and %s", b.Status.State, got, reasonLanded, want)
			}
		})
	}
}

// Tools that write commit objects themselves can make an author that git
// doesn't let a new commit have, or changes when a new commit takes it,
// such as a time zone of +9999. A squash or rebase landing that would copy
// such an author says which commit has it, instead of failing on every
// reconcile or landing a different date. A committer time that git can't
// read doesn't stop a landing, because the new commits have the merge
// controller as their committer.
func TestAuthorsThatGitRefuses(t *testing.T) {
	for name, tt := range map[string]struct {
		author, committer string
		problem           string
	}{
		"no name":           {author: "<ana@example.com> 1700000000 -0800", problem: "author has no name"},
		"NUL in the author": {author: "Ana\x00Lima <ana@example.com> 1700000000 -0800", problem: "author has no name"},
		"only punctuation":  {author: ",;: <ana@example.com> 1700000000 -0800", problem: `author has no name that git accepts, only ",;:"`},
		"no date":           {author: "Ana Lima <ana@example.com>", problem: "author has no date that git can copy"},
		"time zone with five digits": {
			author:  "Ana Lima <ana@example.com> 1700000000 +12345",
			problem: "author has no date that git can copy",
		},
		"time zone with five digits before 1973": {
			author:  "Ana Lima <ana@example.com> 99999999 +12345",
			problem: "author has no date that git can copy",
		},
		"time zone with 99 minutes": {
			author:  "Ana Lima <ana@example.com> 1700000000 +9999",
			problem: "author has no date that git can copy",
		},
		"committer without a date": {
			author:    "Ana Lima <ana@example.com> 1700000000 -0800",
			committer: "Test Author <author@example.com>",
		},
	} {
		for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
			t.Run(name+"/"+landing, func(t *testing.T) {
				srv := gittest.NewServer(t, "")
				b, w := branches(t, srv)
				w.Branch("c/x", b.Spec.ParentHead)
				w.Write("y.txt", "y\n")
				committer := tt.committer
				if committer == "" {
					committer = "Test Author <author@example.com> " + testTime
				}
				odd := commitRaw(t, w, tt.author, committer)
				moveParent(t, b, w, "m.txt", "m\n")
				mergeParent(b, w)
				refresh(t, b, w)
				main := b.Spec.ParentHead
				before := srv.Heads(t, "app")
				if err := landAs(t, srv, b, landing); err != nil {
					t.Fatal(err)
				}
				c := kube.FindCondition(b.Status.Conditions, "Merged")
				if tt.problem == "" {
					if c == nil || c.Reason != reasonLanded {
						t.Errorf("Merged = %+v, want reason %s", c, reasonLanded)
					}
					return
				}
				if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
					t.Errorf("heads = %v, want %v", after, before)
				}
				msg := fmt.Sprintf("can't %s c/x onto main at %s, because %s's %s", strings.ToLower(landing), gitk8s.Short(main), gitk8s.Short(odd), tt.problem)
				if c == nil || c.Status != kube.False || c.Reason != reasonNeedsRebase || c.Message != msg {
					t.Errorf("Merged = %+v, want reason %s and message %q", c, reasonNeedsRebase, msg)
				}
			})
		}
	}
}

// A squash or rebase landing reads at most maxLandingCommits of the
// branch's commits and git.MaxLogBytes of their text, so a branch with more
// needs a person. A branch that the landing keeps as it is still lands by
// fast-forward, because the merge controller doesn't read its commits.
func TestLandingLimits(t *testing.T) {
	type setup func(*testing.T, *gitk8s.GitBranch, *gittest.Work)
	many := func(n int) setup {
		return func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) { commitMany(t, w, n) }
	}
	big := func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) { commitBig(t, w) }
	bigOnParent := func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
		w.Branch("c/x", b.Spec.ParentHead)
		commitBig(t, w)
	}
	merged := func(s setup) setup {
		return func(t *testing.T, b *gitk8s.GitBranch, w *gittest.Work) {
			s(t, b, w)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
		}
	}
	tooMany := "c/x has more than 1000 commits that main doesn't have"
	tooBig := "c/x's commits have more than 8 MiB of messages, names, and other text"
	for name, tt := range map[string]struct {
		landing string
		setup   setup
		// problem is the NeedsRebase message's reason, or "" when the
		// branch lands with a message that starts with verb.
		problem, verb string
	}{
		"squash of 1000 commits":                 {landing: gitk8s.Squash, setup: many(maxLandingCommits - 1), verb: "squashed"},
		"squash of too many commits":             {landing: gitk8s.Squash, setup: merged(many(maxLandingCommits)), problem: tooMany},
		"rebase of too many commits":             {landing: gitk8s.Rebase, setup: merged(many(maxLandingCommits)), problem: tooMany},
		"squash of too much text":                {landing: gitk8s.Squash, setup: merged(big), problem: tooBig},
		"rebase of too much text":                {landing: gitk8s.Rebase, setup: merged(big), problem: tooBig},
		"rebase of many commits without merges":  {landing: gitk8s.Rebase, setup: many(maxLandingCommits), verb: "fast-forwarded"},
		"rebase of a big commit without merges":  {landing: gitk8s.Rebase, setup: big, verb: "fast-forwarded"},
		"squash of one big commit on the parent": {landing: gitk8s.Squash, setup: bigOnParent, verb: "fast-forwarded"},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			tt.setup(t, b, w)
			refresh(t, b, w)
			main, head := b.Spec.ParentHead, b.Spec.Head
			before := srv.Heads(t, "app")
			if err := landAs(t, srv, b, tt.landing); err != nil {
				t.Fatal(err)
			}
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			if tt.problem == "" {
				if c == nil || c.Reason != reasonLanded || !strings.HasPrefix(c.Message, tt.verb+" ") {
					t.Fatalf("Merged = %+v, want reason %s and a message that starts with %q", c, reasonLanded, tt.verb)
				}
				if got, want := w.Git("rev-parse", w.Fetch("main")+"^{tree}"), w.Git("rev-parse", head+"^{tree}"); got != want {
					t.Errorf("main's tree = %s, want the head's tree %s", got, want)
				}
				return
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			msg := fmt.Sprintf("can't %s c/x onto main at %s, because %s", strings.ToLower(tt.landing), gitk8s.Short(main), tt.problem)
			if c == nil || c.Status != kube.False || c.Reason != reasonNeedsRebase || c.Message != msg {
				t.Errorf("Merged = %+v, want reason %s and message %q", c, reasonNeedsRebase, msg)
			}
		})
	}
}

// A remote can refuse to delete a branch or to replace its commits. The
// parent then lands alone, as in a fast-forward landing. A branch that the
// remote won't delete moves to the landed commit if the remote lets it, so
// the next listing shows it as Merged. A branch that stays where it was
// shows Merged once check-base merges the parent into it.
func TestRemoteRefusesTheBranch(t *testing.T) {
	for name, tt := range map[string]struct {
		deny  []string
		keep  bool
		moved bool
		why   string
	}{
		"deletion": {
			deny:  []string{"receive.denyDeletes"},
			moved: true,
			why:   "delete it: [remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/c/x",
		},
		"deletion and force push": {
			deny: []string{"receive.denyDeletes", "receive.denyNonFastForwards"},
			why:  "delete it: [remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/c/x",
		},
		"force push to a branch that stays": {
			deny: []string{"receive.denyNonFastForwards"},
			keep: true,
			why:  "move it: [remote rejected] (non-fast-forward); remote: error: denying non-fast-forward refs/heads/c/x (you should pull first)",
		},
	} {
		for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
			t.Run(name+"/"+landing, func(t *testing.T) {
				srv := gittest.NewServer(t, "")
				b, w := branches(t, srv)
				moveParent(t, b, w, "m.txt", "m\n")
				mergeParent(b, w)
				refresh(t, b, w)
				p := *b.Spec.Merge
				p.DeleteMergedBranches = !tt.keep
				b.Spec.Merge = &p
				for _, key := range tt.deny {
					srv.Config(t, "app", key, "true")
				}
				main, head := b.Spec.ParentHead, b.Spec.Head
				if err := landAs(t, srv, b, landing); err != nil {
					t.Fatal(err)
				}
				heads := srv.Heads(t, "app")
				landed := heads["main"]
				if landed == main || landed == head {
					t.Fatalf("main = %s, want a new commit on %s", landed, main)
				}
				branch, left := head, "left c/x at "+gitk8s.Short(head)
				if tt.moved {
					branch, left = landed, "moved c/x there"
				}
				if heads["c/x"] != branch {
					t.Errorf("c/x = %s, want %s", heads["c/x"], branch)
				}
				verb := map[string]string{gitk8s.Squash: "squashed", gitk8s.Rebase: "rebased"}[landing]
				msg := fmt.Sprintf("%s c/x onto main, which moved from %s to %s, and %s, because the remote refused to %s",
					verb, gitk8s.Short(main), gitk8s.Short(landed), left, tt.why)
				if c := kube.FindCondition(b.Status.Conditions, "Merged"); c == nil || c.Reason != reasonLanded || c.Message != msg {
					t.Errorf("Merged = %+v, want reason %s and message %q", c, reasonLanded, msg)
				}
				if tt.moved {
					b.Spec.Head, b.Spec.ParentHead = landed, landed
				} else {
					b.Spec.ParentHead = w.Fetch("main")
					mergeParent(b, w)
					refresh(t, b, w)
				}
				if err := landAs(t, srv, b, landing); err != nil {
					t.Fatal(err)
				}
				if b.Status.State != reasonMerged {
					t.Errorf("after the next listing, state = %q, want %s", b.Status.State, reasonMerged)
				}
			})
		}
	}
}

// A remote that refuses to replace the branch's commits stops a squash or
// rebase landing from pushing its commit to the branch for the checks. The
// branch needs a person, instead of failing on every reconcile.
func TestRemoteRefusesTheRewrittenBranch(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, b, w)
			withHistoryCheck(b)
			srv.Config(t, "app", "receive.denyNonFastForwards", "true")
			before := srv.Heads(t, "app")
			if err := landAs(t, srv, b, landing); err != nil {
				t.Fatal(err)
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			verb := map[string]string{gitk8s.Squash: "squashed", gitk8s.Rebase: "rebased"}[landing]
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			start, end := "can't push the "+verb+" commit ", " to c/x for dco to check, because the remote refused it: [remote rejected] (non-fast-forward); remote: error: denying non-fast-forward refs/heads/c/x (you should pull first)"
			if c == nil || c.Reason != reasonNeedsRebase || !strings.HasPrefix(c.Message, start) || !strings.HasSuffix(c.Message, end) {
				t.Errorf("Merged = %+v, want reason %s and a message like %q", c, reasonNeedsRebase, start+"..."+end)
			}
		})
	}
}

// When a check's result doesn't have filesOnly, a squash landing pushes the
// squashed commit to the branch for the checks to run on, and lands it by
// fast-forward once they pass.
func TestHistoryResultsRewriteTheBranch(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Write("y.txt", "y\n")
	w.Commit("add y")
	refresh(t, b, w)
	withHistoryCheck(b)
	main, head := b.Spec.ParentHead, b.Spec.Head
	if err := landAs(t, srv, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	heads := srv.Heads(t, "app")
	squashed := heads["c/x"]
	if heads["main"] != main || squashed == head {
		t.Fatalf("main = %s, c/x = %s; want main at %s and a squashed commit on c/x", heads["main"], squashed, main)
	}
	w.Fetch("c/x")
	if got, want := w.Git("rev-parse", squashed+"^", squashed+"^{tree}"), main+"\n"+w.Git("rev-parse", head+"^{tree}"); got != want {
		t.Errorf("squashed commit's parent and tree = %q, want %q", got, want)
	}
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	msg := fmt.Sprintf("squashed c/x onto main at %s as %s and pushed it to c/x, because the results of dco might depend on the branch's commits",
		gitk8s.Short(main), gitk8s.Short(squashed))
	if c == nil || c.Status != kube.False || c.Message != msg || b.Status.State != reasonRewritten {
		t.Errorf("Merged = %+v, state %q", c, b.Status.State)
	}

	t.Log("The checks pass on the squashed commit, which lands by fast-forward.")
	w.Branch("c/x", squashed)
	refresh(t, b, w)
	withHistoryCheck(b)
	if err := landAs(t, srv, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	heads = srv.Heads(t, "app")
	if heads["main"] != squashed {
		t.Errorf("main = %s, want %s", heads["main"], squashed)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	if b.Status.State != reasonLanded {
		t.Errorf("state = %q, want %s", b.Status.State, reasonLanded)
	}
}

// A check whose result doesn't have filesOnly can push a fix to the commit
// that a squash landing pushed to the branch. The merge controller squashes
// again when a person adds a commit, but it lands its own commit and the
// fixes after it by fast-forward. It recognizes its commit even when git
// drops characters from its identity, such as the brackets in an email of
// "<git-k8s@example.com>".
func TestSquashKeepsFixesAfterItsCommit(t *testing.T) {
	for name, id := range map[string]git.Identity{
		"plain":                    {Name: "git-k8s", Email: "git-k8s@example.com"},
		"space and angle brackets": {Name: "git-k8s ", Email: "<git-k8s@example.com>"},
		"quoted name":              {Name: `"git-k8s"`, Email: "git-k8s@example.com"},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			main := b.Spec.ParentHead
			// squash lands c/x by squash, checks that the merge controller
			// pushed a squashed commit to c/x instead, and leaves w on that
			// commit.
			squash := func() {
				t.Helper()
				refresh(t, b, w)
				withHistoryCheck(b)
				head := b.Spec.Head
				if err := landWith(t, srv, b, gitk8s.Squash, id, nil); err != nil {
					t.Fatal(err)
				}
				squashed := w.Fetch("c/x")
				got := w.Git("rev-parse", squashed+"^", squashed+"^{tree}")
				if want := main + "\n" + w.Git("rev-parse", head+"^{tree}"); got != want || b.Status.State != reasonRewritten {
					t.Fatalf("state %q, c/x's parent and tree = %q; want %s and %q", b.Status.State, got, reasonRewritten, want)
				}
				w.Branch("c/x", squashed)
			}

			w.Write("y.txt", "y\n")
			w.Commit("add y")
			squash()

			t.Log("dco pushes a fix, and a person adds a commit, so the branch is squashed again.")
			w.Write("y.txt", "y, fixed\n")
			w.Commit("Fix y\n\nGit-K8s-Fixer: dco")
			w.Write("z.txt", "z\n")
			w.Commit("add z")
			squash()

			t.Log("dco pushes another fix, and the branch lands by fast-forward.")
			w.Write("z.txt", "z, fixed\n")
			w.Commit("Fix z\n\nGit-K8s-Fixer: dco")
			refresh(t, b, w)
			withHistoryCheck(b)
			head := b.Spec.Head
			if err := landWith(t, srv, b, gitk8s.Squash, id, nil); err != nil {
				t.Fatal(err)
			}
			heads := srv.Heads(t, "app")
			if _, ok := heads["c/x"]; heads["main"] != head || ok {
				t.Errorf("heads = %v, want main at %s and no c/x", heads, head)
			}
			c := kube.FindCondition(b.Status.Conditions, "Merged")
			msg := fmt.Sprintf("fast-forwarded main from %s to %s", gitk8s.Short(main), gitk8s.Short(head))
			if c == nil || c.Reason != reasonLanded || c.Message != msg {
				t.Errorf("Merged = %+v, want reason %s and message %q", c, reasonLanded, msg)
			}
		})
	}
}

// The pushes of squash and rebase landings carry leases on the listed heads,
// so nothing changes when a branch moves after it's listed.
func TestRewriteNeedsTheListedHeads(t *testing.T) {
	for name, tt := range map[string]struct {
		move    string
		history bool
	}{
		"branch moved":                      {move: "c/x"},
		"parent moved":                      {move: "main"},
		"branch moved with a history check": {move: "c/x", history: true},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			w.Write("y.txt", "y\n")
			w.Commit("add y")
			refresh(t, b, w)
			if tt.history {
				withHistoryCheck(b)
			}
			from := b.Spec.Head
			if tt.move == "main" {
				from = b.Spec.ParentHead
			}
			w.Branch(tt.move, from)
			w.Write("z.txt", "z\n")
			w.Commit("moves after the listing")
			w.Push(tt.move)
			before := srv.Heads(t, "app")
			if err := landAs(t, srv, b, gitk8s.Squash); err == nil || !strings.Contains(err.Error(), "push rejected") {
				t.Errorf("err = %v, want a rejected push", err)
			}
			if after := srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
		})
	}
}

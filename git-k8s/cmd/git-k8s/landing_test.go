package main

import (
	"fmt"
	"maps"
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
	p := *b.Spec.Merge
	p.Landing = landing
	b.Spec.Merge = &p
	repo, secret := srv.Repository("app", rules()...)
	ctx, _ := kube.Fake(t.Context(), b, repo, secret)
	m := &merger{
		ident: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"},
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
		"base":  {Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed},
		"gofmt": {Commit: b.Spec.Head, State: gitk8s.Passed},
	}
}

// withHistoryCheck adds dco, a check whose passing result uses the branch's
// history, to b's merge policy.
func withHistoryCheck(b *gitk8s.GitBranch) {
	p := *b.Spec.Merge
	p.Checks = append(p.Checks[:len(p.Checks):len(p.Checks)], gitk8s.CheckPolicy{Name: "dco"})
	b.Spec.Merge = &p
	b.Status.Checks["dco"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Passed, UsesHistory: true}
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
		name:    "only fixes",
		log:     []git.LogEntry{merge, fix},
		author:  bo,
		message: fix.Message,
	}, {
		name:    "only a merge",
		log:     []git.LogEntry{{Parents: []string{"p", "q"}, Author: ana, Message: "Merge feature\n"}},
		author:  ana,
		message: "Merge feature\n",
	}} {
		t.Run(tt.name, func(t *testing.T) {
			author, message := squashMessage(tt.log)
			if author != tt.author || message != tt.message {
				t.Errorf("squashMessage = %+v, %q; want %+v, %q", author, message, tt.author, tt.message)
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

// When a check's result uses the branch's history, a squash landing pushes the
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
	msg := fmt.Sprintf("squashed c/x onto main at %s as %s and pushed it to c/x, because the results of dco use the branch's history",
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

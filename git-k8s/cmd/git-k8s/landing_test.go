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
// branches with landing, and then syncs the mirror, which pushes what the
// merge controller changed in its copy to the external repository. The
// policy queues branches, so b is at the front of main's queue at its
// current head.
func landAs(t *testing.T, f *fixture, b *gitk8s.TrackedBranch, landing string) error {
	t.Helper()
	return landWith(t, f, b, landing, git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}, nil)
}

// landWith is landAs with id as the merge controller's identity. If signer
// isn't nil, the TrackedRepository's signing Secret holds its key. Only the
// sync may change the external repository, so landWith fails the test if
// the merge controller does.
func landWith(t *testing.T, f *fixture, b *gitk8s.TrackedBranch, landing string, id git.Identity, signer *gittest.Signer) error {
	t.Helper()
	p := *b.Spec.Merge
	p.Landing = landing
	b.Spec.Merge = &p
	b.Status.Queued = &gitk8s.Queued{Head: b.Spec.Head, Position: 1}
	before := f.srv.Heads(t, "app")
	world := f.world(f.repo, parentOf(b, b.Spec.Branch))
	if signer != nil {
		world = append(world, signer.Sign(f.repo))
	}
	ctx, _ := kube.Fake(t.Context(), b, world...)
	err := (&merger{mirror: f.mirror, ident: id}).Reconcile(ctx, b)
	if after := f.srv.Heads(t, "app"); !maps.Equal(after, before) {
		t.Errorf("the merge controller changed the external repository's heads from %v to %v", before, after)
	}
	if err != nil {
		return err
	}
	f.fetch()
	return nil
}

// branches returns a fixture, its branch c/x from fixture.branches, and
// its working repository.
func branches(t *testing.T) (*fixture, *gitk8s.TrackedBranch, *gittest.Work) {
	t.Helper()
	f := newFixture(t)
	return f, f.branches(), f.work
}

// refresh pushes the working repository's current commit to c/x, syncs the
// mirror, and gives b fresh, passing results for it, like the repositories
// controller and the checks do.
func refresh(t *testing.T, f *fixture, b *gitk8s.TrackedBranch) {
	t.Helper()
	f.work.Push("c/x")
	f.fetch()
	b.Spec.Head = f.work.Git("rev-parse", "HEAD")
	b.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: b.Spec.Head, Scope: gitk8s.ScopeParent, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed, FilesOnly: true},
		"gofmt": {Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Passed, FilesOnly: true},
	}
}

// withHistoryCheck adds dco, a check whose passing result doesn't have
// filesOnly, such as one that reads commit messages, to b's merge policy.
func withHistoryCheck(b *gitk8s.TrackedBranch) {
	dco := gitk8s.CheckPolicy{Name: "dco"}
	if p := *b.Spec.Merge; !slices.Contains(p.Checks, dco) {
		p.Checks = append(p.Checks[:len(p.Checks):len(p.Checks)], dco)
		b.Spec.Merge = &p
	}
	b.Status.Checks["dco"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
}

// moveParent pushes a commit that writes a file to main, and leaves w on c/x.
func moveParent(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work, path, content string) {
	t.Helper()
	head := w.Git("rev-parse", "HEAD")
	w.Branch("main", b.Spec.ParentHead)
	w.Write(path, content)
	b.Spec.ParentHead = w.Commit("main moves")
	w.Push("main")
	w.Branch("c/x", head)
}

// mergeParent merges main into c/x, like check-base.
func mergeParent(b *gitk8s.TrackedBranch, w *gittest.Work) {
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
	f, b, w := branches(t)
	w.Write("y.txt", "y\n")
	commitAsAna(w, "Add y\n\nWith a body.\n\nSigned-off-by: Ana Lima <ana@example.com>")
	moveParent(t, b, w, "m.txt", "m\n")
	mergeParent(b, w)
	w.Write("x.txt", "x, formatted\n")
	w.Commit("Format Go files with gofmt\n\nGit-K8s-Fixer: gofmt")
	refresh(t, f, b)
	main := b.Spec.ParentHead
	if err := landAs(t, f, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	if _, ok := f.srv.Heads(t, "app")["c/x"]; ok {
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
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	msg := fmt.Sprintf("squashed c/x onto main, which moved from %s to %s", gitk8s.Short(main), gitk8s.Short(squashed))
	if c == nil || c.Status != kube.True || c.Message != msg || b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("Landed = %+v, state %q", c, b.Status.State)
	}
}

// TestSquashKeepsAgentTrailers squashes a person's commit and an agent's
// fix. check-risk's results count for the squashed commit, so it must still
// count as a change from an agent.
func TestSquashKeepsAgentTrailers(t *testing.T) {
	f, b, w := branches(t)
	w.Write("x.txt", "x, reviewed\n")
	w.Commit("Apply changes from the review agent\n\nFix x.\n\nx.txt\n\nGit-K8s-Fixer: review\nGit-K8s-Agent: review")
	refresh(t, f, b)
	main := b.Spec.ParentHead
	if err := landAs(t, f, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	squashed := w.Fetch("main")
	if got, want := w.Git("log", "-1", "--format=%B", squashed), "add x\n\nGit-K8s-Agent: review"; got != want {
		t.Errorf("squashed message = %q, want %q", got, want)
	}
	repo, err := (&git.Git{}).Open(t.Context(), filepath.Join(w.Dir, ".git"))
	if err != nil {
		t.Fatal(err)
	}
	for _, head := range []string{b.Spec.Head, squashed} {
		if n, err := repo.CountCommits(t.Context(), main, head, git.AgentTrailer); err != nil || n != 1 {
			t.Errorf("CountCommits(%s, %s) = %d, %v; want 1", gitk8s.Short(main), gitk8s.Short(head), n, err)
		}
	}
}

func TestSquashMessage(t *testing.T) {
	ana := git.Signature{Name: "Ana Lima", Email: "ana@example.com", Date: "1700000000 -0800"}
	bo := git.Signature{Name: "Bo Chen", Email: "bo@example.com", Date: "1700000100 +0000"}
	anaSigned := "Signed-off-by: Ana Lima <ana@example.com>"
	fix := git.LogEntry{Parents: []string{"p"}, Author: bo, Message: "Format Go files with gofmt\n\nGit-K8s-Fixer: gofmt\n", Trailers: []string{"Git-K8s-Fixer: gofmt"}}
	merge := git.LogEntry{Parents: []string{"p", "q"}, Author: bo, Message: "Merge main into c/x\n\nGit-K8s-Fixer: base\n", Trailers: []string{"Git-K8s-Fixer: base"}}
	agentFix := func(name string) git.LogEntry {
		return git.LogEntry{
			Parents:  []string{"p"},
			Author:   bo,
			Message:  "Apply changes from the " + name + " agent\n\nFix it.\n\nGit-K8s-Fixer: " + name + "\nGit-K8s-Agent: " + name + "\n",
			Trailers: []string{"Git-K8s-Fixer: " + name, "Git-K8s-Agent: " + name},
		}
	}
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
	}, {
		name:    "one person's commit and an agent's fix",
		log:     []git.LogEntry{{Parents: []string{"p"}, Author: ana, Message: "Add y\n\nWith a body.\n"}, agentFix("review")},
		author:  ana,
		message: "Add y\n\nWith a body.\n\nGit-K8s-Agent: review\n",
	}, {
		name: "one person's commit with a trailer, agents' fixes, and a merge with the agent trailer",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\n" + anaSigned + "\n", Trailers: []string{anaSigned}},
			agentFix("review"),
			{Parents: []string{"p", "q"}, Author: bo, Message: "Merge main into c/x\n\nGit-K8s-Fixer: base\nGit-K8s-Agent: base\n", Trailers: []string{"Git-K8s-Fixer: base", "Git-K8s-Agent: base"}},
			agentFix("deps"),
			agentFix("review"),
		},
		author:  ana,
		message: "Add y\n\n" + anaSigned + "\nGit-K8s-Agent: review\nGit-K8s-Agent: base\nGit-K8s-Agent: deps\n",
	}, {
		name: "one person's commit with only a trailer like the fixer trailer, and an agent's fix",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\ngit-k8s-fixer: x\n", Trailers: []string{"git-k8s-fixer: x"}},
			agentFix("review"),
		},
		author:  ana,
		message: "Add y\n\nGit-K8s-Agent: review\n",
	}, {
		name: "one person's commit with the agent trailer",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\nGit-K8s-Agent: review\n", Trailers: []string{"Git-K8s-Agent: review"}},
			{
				Parents:  []string{"p"},
				Author:   bo,
				Message:  "Apply changes from the review agent\n\nGit-K8s-Fixer: review\nGit-K8s-Agent: review  \n",
				Trailers: []string{"Git-K8s-Fixer: review", "Git-K8s-Agent: review"},
			},
		},
		author:  ana,
		message: "Add y\n\nGit-K8s-Agent: review\n",
	}, {
		name: "several commits and agents' fixes",
		log: []git.LogEntry{
			{Parents: []string{"p"}, Author: ana, Message: "Add y\n\n" + anaSigned + "\n", Trailers: []string{anaSigned}},
			agentFix("review"),
			{Parents: []string{"p"}, Author: bo, Message: "Add z\n"},
			agentFix("review"),
		},
		author: ana,
		message: "Add y\n\n* Add y\n* Apply changes from the review agent\n* Add z\n* Apply changes from the review agent\n\n" +
			anaSigned + "\nGit-K8s-Agent: review\nCo-authored-by: Bo Chen <bo@example.com>\n",
	}, {
		name:    "only an agent's fix",
		log:     []git.LogEntry{merge, agentFix("review")},
		author:  bo,
		message: "Apply changes from the review agent\n\nFix it.\n\nGit-K8s-Agent: review\n",
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
	f, b, w := branches(t)
	w.Write("y.txt", "y\n")
	commitAsAna(w, "Add y\n\nWith a body.")
	moveParent(t, b, w, "m.txt", "m\n")
	mergeParent(b, w)
	w.Write("z.txt", "z\n")
	w.Commit("add z")
	refresh(t, f, b)
	main := b.Spec.ParentHead
	if err := landAs(t, f, b, gitk8s.Rebase); err != nil {
		t.Fatal(err)
	}
	if _, ok := f.srv.Heads(t, "app")["c/x"]; ok {
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
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	msg := fmt.Sprintf("rebased c/x onto main, which moved from %s to %s", gitk8s.Short(main), gitk8s.Short(rebased))
	if c == nil || c.Status != kube.True || c.Message != msg || b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("Landed = %+v, state %q", c, b.Status.State)
	}
}

// Squash and rebase landings sign the commits that they make with the
// TrackedRepository's key, including the squashed or rebased commits that the
// merge controller pushes to the branch for the checks.
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
		{"rebase for the checks", gitk8s.Rebase, true, "c/x", 2},
	} {
		t.Run(tt.name, func(t *testing.T) {
			f, b, w := branches(t)
			w.Write("y.txt", "y\n")
			commitAsAna(w, "Add y")
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, f, b)
			if tt.history {
				withHistoryCheck(b)
			}
			main := b.Spec.ParentHead
			if err := landWith(t, f, b, tt.landing, id, signer); err != nil {
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

// A landing that can't read the signing key changes nothing in the mirror's
// copy, but a landing that makes no commits doesn't read the key.
func TestLandingNeedsTheSigningKey(t *testing.T) {
	broken := &gittest.Signer{Email: "git-k8s@example.com", Key: []byte("hunter2")}
	id := git.Identity{Name: "git-k8s", Email: broken.Email}
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			f, b, w := branches(t)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, f, b)
			before := f.mirrorHeads()
			err := landWith(t, f, b, landing, id, broken)
			if err == nil || !strings.Contains(err.Error(), "reading the signing key: Secret app-signing: the key isn't a private key") || strings.Contains(err.Error(), "hunter2") {
				t.Fatalf("err = %v, want one that says the signing key isn't a key, without the Secret's data", err)
			}
			if after := f.mirrorHeads(); !maps.Equal(after, before) {
				t.Errorf("the mirror's heads = %v, want %v", after, before)
			}

			moveParent(t, b, w, "x.txt", "x\n")
			mergeParent(b, w)
			refresh(t, f, b)
			if err := landWith(t, f, b, landing, id, broken); err != nil || b.Status.State != gitk8s.MergeStateNothingToLand {
				t.Errorf("landing a branch whose changes the parent has: state %q, %v; want %s", b.Status.State, err, gitk8s.MergeStateNothingToLand)
			}
		})
	}
}

// A rebase landing leaves out a commit whose change the parent already has.
func TestRebaseLeavesOutChangesInTheParent(t *testing.T) {
	f, b, w := branches(t)
	w.Write("y.txt", "y\n")
	w.Commit("add y")
	moveParent(t, b, w, "y.txt", "y\n")
	mergeParent(b, w)
	refresh(t, f, b)
	main := b.Spec.ParentHead
	if err := landAs(t, f, b, gitk8s.Rebase); err != nil {
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
			f, b, w := branches(t)
			if landing == gitk8s.Rebase {
				w.Write("y.txt", "y\n")
				w.Commit("add y")
				refresh(t, f, b)
			}
			main, head := b.Spec.ParentHead, b.Spec.Head
			if err := landAs(t, f, b, landing); err != nil {
				t.Fatal(err)
			}
			heads := f.srv.Heads(t, "app")
			if heads["main"] != head {
				t.Errorf("main = %s, want %s", heads["main"], head)
			}
			if _, ok := heads["c/x"]; ok {
				t.Error("c/x wasn't deleted after it landed")
			}
			c := kube.FindCondition(b.Status.Conditions, "Landed")
			msg := fmt.Sprintf("fast-forwarded main from %s to %s", gitk8s.Short(main), gitk8s.Short(head))
			if c == nil || c.Reason != string(gitk8s.MergeStateLanded) || c.Message != msg {
				t.Errorf("Landed = %+v", c)
			}
		})
	}
}

// Without deleteLandedBranches, the branch moves to the landed commit in the
// same update, so it stays in its parent.
func TestRewriteMovesAKeptBranch(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			f, b, w := branches(t)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, f, b)
			p := *b.Spec.Merge
			p.DeleteLandedBranches = false
			b.Spec.Merge = &p
			main := b.Spec.ParentHead
			if err := landAs(t, f, b, landing); err != nil {
				t.Fatal(err)
			}
			heads := f.srv.Heads(t, "app")
			if heads["main"] == main || heads["main"] == b.Spec.Head || heads["c/x"] != heads["main"] {
				t.Errorf("main = %s, c/x = %s; want both at a new commit on %s", heads["main"], heads["c/x"], main)
			}
			if b.Status.State != gitk8s.MergeStateLanded {
				t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateLanded)
			}
		})
	}
}

// A branch whose changes the parent already has leaves the parent as it is.
func TestRewriteWithNothingToLand(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			f, b, w := branches(t)
			moveParent(t, b, w, "x.txt", "x\n")
			mergeParent(b, w)
			refresh(t, f, b)
			before := f.srv.Heads(t, "app")
			if err := landAs(t, f, b, landing); err != nil {
				t.Fatal(err)
			}
			if after := f.srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			c := kube.FindCondition(b.Status.Conditions, "Landed")
			if c == nil || c.Status != kube.False || b.Status.State != gitk8s.MergeStateNothingToLand {
				t.Errorf("Landed = %+v, state %q", c, b.Status.State)
			}
		})
	}
}

// A branch that a rebase can't copy needs a person, but a squash landing
// lands it, because it only needs the head's files.
func TestRebaseNeedsRebase(t *testing.T) {
	for name, tt := range map[string]struct {
		setup   func(*testing.T, *gitk8s.TrackedBranch, *gittest.Work)
		problem string
	}{
		"conflict resolved in a merge": {
			setup: func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) {
				moveParent(t, b, w, "x.txt", "main\n")
				w.Git("merge", "--quiet", "--no-commit", "-s", "ours", b.Spec.ParentHead)
				w.Write("x.txt", "x\nmain\n")
				w.Commit("Merge main into c/x")
			},
			problem: "conflicts in x.txt",
		},
		"merge that changes files": {
			setup: func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) {
				moveParent(t, b, w, "m.txt", "m\n")
				w.Git("merge", "--quiet", "--no-commit", "--no-ff", b.Spec.ParentHead)
				w.Write("e.txt", "e\n")
				w.Commit("Merge main into c/x")
			},
			problem: "because merge commits in the branch change files, and a rebase leaves merges out",
		},
		"unrelated history": {
			setup: func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) {
				root := w.Git("commit-tree", "4b825dc642cb6eb9a060e54bf8d69288fbee4904", "-m", "unrelated")
				w.Git("merge", "--quiet", "--allow-unrelated-histories", "-m", "Merge unrelated", root)
			},
			problem: "has no parent",
		},
	} {
		t.Run(name, func(t *testing.T) {
			f, b, w := branches(t)
			tt.setup(t, b, w)
			refresh(t, f, b)
			results := b.Status.Checks
			before := f.srv.Heads(t, "app")
			if err := landAs(t, f, b, gitk8s.Rebase); err != nil {
				t.Fatal(err)
			}
			if after := f.srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			c := kube.FindCondition(b.Status.Conditions, "Landed")
			if c == nil || c.Status != kube.False || c.Reason != string(gitk8s.MergeStateNeedsRebase) || !strings.Contains(c.Message, tt.problem) {
				t.Errorf("Landed = %+v, want reason %s and a message with %q", c, gitk8s.MergeStateNeedsRebase, tt.problem)
			}

			b.Generation++
			b.Status.Checks = results
			if err := landAs(t, f, b, gitk8s.Squash); err != nil {
				t.Fatal(err)
			}
			squashed := w.Fetch("main")
			if got, want := w.Git("rev-parse", squashed+"^{tree}"), w.Git("rev-parse", b.Spec.Head+"^{tree}"); got != want || b.Status.State != gitk8s.MergeStateLanded {
				t.Errorf("after a squash landing, state = %q and main's tree = %s, want %s and %s", b.Status.State, got, gitk8s.MergeStateLanded, want)
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
				f, b, w := branches(t)
				w.Branch("c/x", b.Spec.ParentHead)
				w.Write("y.txt", "y\n")
				committer := tt.committer
				if committer == "" {
					committer = "Test Author <author@example.com> " + testTime
				}
				odd := commitRaw(t, w, tt.author, committer)
				moveParent(t, b, w, "m.txt", "m\n")
				mergeParent(b, w)
				refresh(t, f, b)
				main := b.Spec.ParentHead
				before := f.srv.Heads(t, "app")
				if err := landAs(t, f, b, landing); err != nil {
					t.Fatal(err)
				}
				c := kube.FindCondition(b.Status.Conditions, "Landed")
				if tt.problem == "" {
					if c == nil || c.Reason != string(gitk8s.MergeStateLanded) {
						t.Errorf("Landed = %+v, want reason %s", c, gitk8s.MergeStateLanded)
					}
					return
				}
				if after := f.srv.Heads(t, "app"); !maps.Equal(after, before) {
					t.Errorf("heads = %v, want %v", after, before)
				}
				msg := fmt.Sprintf("can't %s c/x onto main at %s, because %s's %s", strings.ToLower(landing), gitk8s.Short(main), gitk8s.Short(odd), tt.problem)
				if c == nil || c.Status != kube.False || c.Reason != string(gitk8s.MergeStateNeedsRebase) || c.Message != msg {
					t.Errorf("Landed = %+v, want reason %s and message %q", c, gitk8s.MergeStateNeedsRebase, msg)
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
	type setup func(*testing.T, *gitk8s.TrackedBranch, *gittest.Work)
	many := func(n int) setup {
		return func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) { commitMany(t, w, n) }
	}
	big := func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) { commitBig(t, w) }
	bigOnParent := func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) {
		w.Branch("c/x", b.Spec.ParentHead)
		commitBig(t, w)
	}
	merged := func(s setup) setup {
		return func(t *testing.T, b *gitk8s.TrackedBranch, w *gittest.Work) {
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
			f, b, w := branches(t)
			tt.setup(t, b, w)
			refresh(t, f, b)
			main, head := b.Spec.ParentHead, b.Spec.Head
			before := f.srv.Heads(t, "app")
			if err := landAs(t, f, b, tt.landing); err != nil {
				t.Fatal(err)
			}
			c := kube.FindCondition(b.Status.Conditions, "Landed")
			if tt.problem == "" {
				if c == nil || c.Reason != string(gitk8s.MergeStateLanded) || !strings.HasPrefix(c.Message, tt.verb+" ") {
					t.Fatalf("Landed = %+v, want reason %s and a message that starts with %q", c, gitk8s.MergeStateLanded, tt.verb)
				}
				if got, want := w.Git("rev-parse", w.Fetch("main")+"^{tree}"), w.Git("rev-parse", head+"^{tree}"); got != want {
					t.Errorf("main's tree = %s, want the head's tree %s", got, want)
				}
				return
			}
			if after := f.srv.Heads(t, "app"); !maps.Equal(after, before) {
				t.Errorf("heads = %v, want %v", after, before)
			}
			msg := fmt.Sprintf("can't %s c/x onto main at %s, because %s", strings.ToLower(tt.landing), gitk8s.Short(main), tt.problem)
			if c == nil || c.Status != kube.False || c.Reason != string(gitk8s.MergeStateNeedsRebase) || c.Message != msg {
				t.Errorf("Landed = %+v, want reason %s and message %q", c, gitk8s.MergeStateNeedsRebase, msg)
			}
		})
	}
}

// An external repository can refuse to delete a branch or to replace its
// commits. The landing in the mirror's copy doesn't depend on that, so the
// parent lands, and the sync pushes it to the external repository. The
// external repository keeps the branch where it was, and ExternalSynced
// says why.
func TestExternalRepositoryRefusesTheBranch(t *testing.T) {
	for name, tt := range map[string]struct {
		deny string
		keep bool
		why  string
	}{
		"deletion":                          {deny: "receive.denyDeletes", why: "[remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/c/x"},
		"force push to a branch that stays": {deny: "receive.denyNonFastForwards", keep: true, why: "[remote rejected] (non-fast-forward); remote: error: denying non-fast-forward refs/heads/c/x (you should pull first)"},
	} {
		for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
			t.Run(name+"/"+landing, func(t *testing.T) {
				f, b, w := branches(t)
				moveParent(t, b, w, "m.txt", "m\n")
				mergeParent(b, w)
				refresh(t, f, b)
				p := *b.Spec.Merge
				p.DeleteLandedBranches = !tt.keep
				b.Spec.Merge = &p
				f.srv.Config(t, "app", tt.deny, "true")
				main, head := b.Spec.ParentHead, b.Spec.Head
				if err := landAs(t, f, b, landing); err != nil {
					t.Fatal(err)
				}
				copied := f.mirrorHeads()
				landed := copied["main"]
				if landed == main || landed == head {
					t.Fatalf("main = %s in the mirror, want a new commit on %s", landed, main)
				}
				branch := ""
				if tt.keep {
					branch = landed
				}
				if copied["c/x"] != branch {
					t.Errorf("c/x = %q in the mirror, want %q", copied["c/x"], branch)
				}
				verb := map[string]string{gitk8s.Squash: "squashed", gitk8s.Rebase: "rebased"}[landing]
				msg := fmt.Sprintf("%s c/x onto main, which moved from %s to %s", verb, gitk8s.Short(main), gitk8s.Short(landed))
				if c := kube.FindCondition(b.Status.Conditions, "Landed"); c == nil || c.Reason != string(gitk8s.MergeStateLanded) || c.Message != msg {
					t.Errorf("Landed = %+v, want reason %s and message %q", c, gitk8s.MergeStateLanded, msg)
				}
				if heads := f.srv.Heads(t, "app"); heads["main"] != landed || heads["c/x"] != head {
					t.Errorf("external heads = %v, want main at %s and c/x at %s", heads, landed, head)
				}
				want := "the external repository refused updates to c/x (" + tt.why + ")"
				if c := f.condition("ExternalSynced"); c == nil || c.Status != kube.False || c.Message != want {
					t.Errorf("ExternalSynced = %+v, want False and message %q", c, want)
				}
			})
		}
	}
}

// An external repository that refuses to replace the branch's commits
// doesn't stop a squash or rebase landing whose gate needs results for the
// new commits, because the merge controller moves the branch in the
// mirror's copy, where the checks run. The external repository keeps the
// branch's old head, and ExternalSynced says why, until the branch lands
// and the sync deletes it there.
func TestExternalRepositoryRefusesTheRewrittenBranch(t *testing.T) {
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		t.Run(landing, func(t *testing.T) {
			f, b, w := branches(t)
			moveParent(t, b, w, "m.txt", "m\n")
			mergeParent(b, w)
			refresh(t, f, b)
			withHistoryCheck(b)
			f.srv.Config(t, "app", "receive.denyNonFastForwards", "true")
			main, head := b.Spec.ParentHead, b.Spec.Head
			if err := landAs(t, f, b, landing); err != nil {
				t.Fatal(err)
			}
			rewritten := f.mirrorHeads()["c/x"]
			if b.Status.State != gitk8s.MergeStateRewritten || rewritten == head {
				t.Fatalf("state %q, c/x = %s in the mirror; want %s and a new commit", b.Status.State, rewritten, gitk8s.MergeStateRewritten)
			}
			if heads := f.srv.Heads(t, "app"); heads["main"] != main || heads["c/x"] != head {
				t.Errorf("external heads = %v, want main at %s and c/x at %s", heads, main, head)
			}
			want := "the external repository refused updates to c/x ([remote rejected] (non-fast-forward); remote: error: denying non-fast-forward refs/heads/c/x (you should pull first))"
			if c := f.condition("ExternalSynced"); c == nil || c.Status != kube.False || c.Message != want {
				t.Errorf("ExternalSynced = %+v, want False and message %q", c, want)
			}

			t.Log("The checks pass on the new commit in the mirror, which lands by fast-forward.")
			b.Generation++
			b.Spec.Head = rewritten
			b.Status.Checks = map[string]gitk8s.CheckResult{
				"base":  {Commit: rewritten, Scope: gitk8s.ScopeParent, ParentCommit: main, State: gitk8s.Passed, FilesOnly: true},
				"gofmt": {Commit: rewritten, Scope: gitk8s.ScopeHead, State: gitk8s.Passed, FilesOnly: true},
				"dco":   {Commit: rewritten, Scope: gitk8s.ScopeHead, State: gitk8s.Passed},
			}
			if err := landAs(t, f, b, landing); err != nil {
				t.Fatal(err)
			}
			if heads := f.srv.Heads(t, "app"); heads["main"] != rewritten || heads["c/x"] != "" {
				t.Errorf("external heads = %v, want main at %s and no c/x", heads, rewritten)
			}
			if c := f.condition("ExternalSynced"); c == nil || c.Status != kube.True {
				t.Errorf("ExternalSynced = %+v, want True", c)
			}
		})
	}
}

// When a check's result doesn't have filesOnly, a squash landing moves the
// branch to the squashed commit for the checks to run on, and lands it by
// fast-forward once they pass.
func TestHistoryResultsRewriteTheBranch(t *testing.T) {
	f, b, w := branches(t)
	w.Write("y.txt", "y\n")
	w.Commit("add y")
	refresh(t, f, b)
	withHistoryCheck(b)
	main, head := b.Spec.ParentHead, b.Spec.Head
	if err := landAs(t, f, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	heads := f.srv.Heads(t, "app")
	squashed := heads["c/x"]
	if heads["main"] != main || squashed == head {
		t.Fatalf("main = %s, c/x = %s; want main at %s and a squashed commit on c/x", heads["main"], squashed, main)
	}
	w.Fetch("c/x")
	if got, want := w.Git("rev-parse", squashed+"^", squashed+"^{tree}"), main+"\n"+w.Git("rev-parse", head+"^{tree}"); got != want {
		t.Errorf("squashed commit's parent and tree = %q, want %q", got, want)
	}
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	msg := fmt.Sprintf("squashed c/x onto main at %s as %s and moved c/x there, because the results of dco might depend on the branch's commits",
		gitk8s.Short(main), gitk8s.Short(squashed))
	if c == nil || c.Status != kube.False || c.Message != msg || b.Status.State != gitk8s.MergeStateRewritten {
		t.Errorf("Landed = %+v, state %q", c, b.Status.State)
	}

	t.Log("The checks pass on the squashed commit, which lands by fast-forward.")
	w.Branch("c/x", squashed)
	b.Generation++
	refresh(t, f, b)
	withHistoryCheck(b)
	if err := landAs(t, f, b, gitk8s.Squash); err != nil {
		t.Fatal(err)
	}
	heads = f.srv.Heads(t, "app")
	if heads["main"] != squashed {
		t.Errorf("main = %s, want %s", heads["main"], squashed)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	if b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateLanded)
	}
}

// A check whose result doesn't have filesOnly can push a fix to the commit
// that a squash landing moved the branch to. The merge controller squashes
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
			f, b, w := branches(t)
			main := b.Spec.ParentHead
			// squash lands c/x by squash, checks that the merge controller
			// moved c/x to a squashed commit instead, and leaves w on that
			// commit.
			squash := func() {
				t.Helper()
				b.Generation++
				refresh(t, f, b)
				withHistoryCheck(b)
				head := b.Spec.Head
				if err := landWith(t, f, b, gitk8s.Squash, id, nil); err != nil {
					t.Fatal(err)
				}
				squashed := w.Fetch("c/x")
				got := w.Git("rev-parse", squashed+"^", squashed+"^{tree}")
				if want := main + "\n" + w.Git("rev-parse", head+"^{tree}"); got != want || b.Status.State != gitk8s.MergeStateRewritten {
					t.Fatalf("state %q, c/x's parent and tree = %q; want %s and %q", b.Status.State, got, gitk8s.MergeStateRewritten, want)
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
			b.Generation++
			refresh(t, f, b)
			withHistoryCheck(b)
			head := b.Spec.Head
			if err := landWith(t, f, b, gitk8s.Squash, id, nil); err != nil {
				t.Fatal(err)
			}
			heads := f.srv.Heads(t, "app")
			if _, ok := heads["c/x"]; heads["main"] != head || ok {
				t.Errorf("heads = %v, want main at %s and no c/x", heads, head)
			}
			c := kube.FindCondition(b.Status.Conditions, "Landed")
			msg := fmt.Sprintf("fast-forwarded main from %s to %s", gitk8s.Short(main), gitk8s.Short(head))
			if c == nil || c.Reason != string(gitk8s.MergeStateLanded) || c.Message != msg {
				t.Errorf("Landed = %+v, want reason %s and message %q", c, gitk8s.MergeStateLanded, msg)
			}
		})
	}
}

// The ref updates of squash and rebase landings carry leases on the listed
// heads, so nothing changes when a branch moves in the mirror after it's
// listed.
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
			f, b, w := branches(t)
			w.Write("y.txt", "y\n")
			w.Commit("add y")
			refresh(t, f, b)
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
			f.fetch()
			before := f.mirrorHeads()
			if err := landAs(t, f, b, gitk8s.Squash); err == nil || !strings.Contains(err.Error(), "push rejected") {
				t.Errorf("err = %v, want a rejected update", err)
			}
			if after := f.mirrorHeads(); !maps.Equal(after, before) {
				t.Errorf("heads in the mirror = %v, want %v", after, before)
			}
		})
	}
}

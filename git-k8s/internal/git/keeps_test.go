package git_test

import (
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestKeeps(t *testing.T) {
	ctx := t.Context()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	var branches []string
	// keep pushes the current commit, so that the repository that Keeps
	// reads can fetch it, and returns the commit.
	keep := func() string {
		t.Helper()
		branches = append(branches, "keep"+strconv.Itoa(len(branches)))
		w.Push(branches[len(branches)-1])
		return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	}
	// commit commits files on top of from. An empty content removes the
	// file.
	commit := func(from, message string, files map[string]string) string {
		t.Helper()
		w.Branch("work", from)
		for path, content := range files {
			if content == "" {
				w.Git("rm", "--quiet", "--end-of-options", path)
			} else {
				w.Write(path, content)
			}
		}
		w.Commit(message)
		return keep()
	}
	pick := func(from string, commits ...string) string {
		t.Helper()
		w.Branch("work", from)
		for _, c := range commits {
			w.Git("cherry-pick", "--end-of-options", c)
		}
		return keep()
	}
	merge := func(from, other string) string {
		t.Helper()
		w.Branch("work", from)
		w.Git("merge", "--quiet", "--no-edit", "--end-of-options", other)
		return keep()
	}

	w.Write("a.txt", "1\n2\n3\n4\n5\n6\n7\n8\n9\n")
	w.Write("c.txt", "foo\nb\nc\nd\nfoo\n")
	w.Write("d.txt", "d\n")
	w.Commit("start")
	start := keep()
	// The sides last agreed at base. Most cases move one of them from side,
	// which only added a commit since then, to head.
	base := commit(start, "add a secret", map[string]string{"r.txt": "secret\n"})
	side := commit(base, "change the first foo", map[string]string{"c.txt": "bar\nb\nc\nd\nfoo\n"})
	ahead := commit(side, "add h", map[string]string{"h.txt": "h\n"})
	sibling := pick(commit(base, "add h", map[string]string{"h.txt": "h\n"}), side)
	replayed := pick(start, side)
	nearby := pick(commit(start, "change c", map[string]string{"c.txt": "foo\nb\nC\nd\nfoo\n"}), side)
	elsewhere := commit(start, "change the last foo", map[string]string{"c.txt": "foo\nb\nc\nd\nbar\n"})
	squashed := commit(start, "change the first foo and add h", map[string]string{"c.txt": "bar\nb\nc\nd\nfoo\n", "h.txt": "h\n"})
	w.Branch("work", replayed)
	for i := range 100 {
		w.Git("commit", "--quiet", "--allow-empty", "-m", "later "+strconv.Itoa(i))
	}
	later := keep()
	m := commit(base, "add m", map[string]string{"m.txt": "m\n"})
	sideMerge := merge(side, m)
	bothReplayed := pick(start, side, m)
	sideEmpty := commit(side, "change nothing", nil)
	replayedEmpty := commit(replayed, "change nothing either", nil)
	x1 := commit(base, "add x", map[string]string{"a.txt": "1\n2\n3\n4\n5\n6\n7\n8\n9\nx\n"})
	x2 := commit(x1, "add another x", map[string]string{"a.txt": "1\n2\n3\n4\n5\n6\n7\n8\n9\nx\nx\n"})
	twice := pick(start, x1, x2)
	once := commit(pick(start, x1), "add another x and h", map[string]string{"a.txt": "1\n2\n3\n4\n5\n6\n7\n8\n9\nx\nx\n", "h.txt": "h\n"})
	dropped := commit(base, "remove d", map[string]string{"d.txt": ""})
	readded := commit(pick(start, dropped), "add d again", map[string]string{"d.txt": "new d\n"})
	cut := commit(base, "remove 2", map[string]string{"a.txt": "1\n3\n4\n5\n6\n7\n8\n9\n"})
	union := commit(pick(start, cut), "bring 2 back as two",
		map[string]string{"a.txt": "1\ntwo\n3\n4\n5\n6\n7\n8\n9\n", ".gitattributes": "a.txt merge=union\n"})
	// A side that rewound to a new commit, which removed the secret.
	rewound := commit(start, "rewind", map[string]string{"c.txt": "bar\nb\nc\nd\nfoo\n"})
	resolved := commit(rewound, "change bar", map[string]string{"c.txt": "baz\nb\nc\nd\nfoo\n"})
	reintroduced := pick(resolved, base)
	smuggled := commit(rewound, "add the secret and h", map[string]string{"r.txt": "secret\n", "h.txt": "h\n"})
	replaced := commit(start, "replace the secret", map[string]string{"r.txt": "placeholder\n"})
	onReplaced := commit(replaced, "add h", map[string]string{"h.txt": "h\n"})
	copied := commit(start, "add the secret again", map[string]string{"r.txt": "secret\n"})
	brought := merge(rewound, copied)
	other := commit(start, "add u", map[string]string{"u.txt": "u\n"})
	joined := merge(rewound, other)
	qux := commit(start, "change the first foo to qux", map[string]string{"c.txt": "qux\nb\nc\nd\nfoo\n"})
	w.Branch("work", rewound)
	w.Git("merge", "--quiet", "--no-edit", "-X", "theirs", "--end-of-options", qux)
	overridden := keep()
	revived := pick(commit(base, "remove the secret", map[string]string{"r.txt": ""}), side)
	// A token and its removal undo each other, so no merge shows a replay
	// of the token. rewound removed both since revoked.
	token := commit(start, "add a token", map[string]string{"t.txt": "token\n"})
	revoked := commit(token, "remove the token", map[string]string{"t.txt": ""})
	tokens := pick(rewound, token, revoked)
	leaked := commit(pick(rewound, token), "add h", map[string]string{"h.txt": "h\n"})
	mergedTokens := merge(rewound, pick(other, token, revoked))
	replayedToken := pick(other, rewound, token)
	tokenAgain := pick(rewound, token)
	leakedAgain := pick(commit(rewound, "add h", map[string]string{"h.txt": "h\n"}), token)
	undone := commit(side, "change the first bar back", map[string]string{"c.txt": "foo\nb\nc\nd\nfoo\n"})
	w.Git("checkout", "--quiet", "--orphan", "lone")
	w.Commit("start over")
	lone := keep()

	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), branches...); err != nil {
		t.Fatal(err)
	}
	for _, c := range []struct {
		name             string
		head, side, base string
		want             bool
	}{
		{"a head that contains the side", ahead, side, base, true},
		{"a head that contains base and replays the side", sibling, side, base, false},
		{"a head that rewound and replays the side", replayed, side, base, true},
		{"a head that rewound and replays the side next to a change of its own", nearby, side, base, true},
		{"a head that rewound and makes the change on another line", elsewhere, side, base, false},
		{"a head that rewound and makes the change in a commit that also adds a file", squashed, side, base, false},
		{"a head that rewound and replays the side under 100 commits", later, side, base, true},
		{"a head that replays each commit of a side that merged", bothReplayed, sideMerge, base, false},
		{"a head with an empty commit for a side's empty commit", replayedEmpty, sideEmpty, base, false},
		{"a head that replays a side's two commits that make the same change", twice, x2, base, true},
		{"a head that replays one of a side's two commits that make the same change", once, x2, base, false},
		{"a head that replays a side's removal of a file and adds the file back", readded, dropped, base, false},
		{"a head that replays a side's removal of a line and adds the line back", union, cut, base, false},
		{"a head built on a side that rewound, changing the side's change", resolved, rewound, base, true},
		{"a head built on a side that rewound, changing the side's change and replaying what the side removed", reintroduced, rewound, base, false},
		{"a head built on a side that rewound, with a commit that brings back what the side removed and adds a file", smuggled, rewound, base, false},
		{"a head built on a side that rewound and changed what it removed", onReplaced, replaced, base, true},
		{"a head that merges a side that rewound with a copy of what it removed", brought, rewound, base, false},
		{"a head that merges a side that rewound with another commit", joined, rewound, base, true},
		{"a head that merges a side that rewound with a commit that overrides the side's change", overridden, rewound, base, false},
		{"a head that replays a side that rewound", replayed, rewound, base, true},
		{"a head with a commit that a side that rewound removed, though not its change", revived, rewound, base, false},
		{"a head with a copy of what a side that reset removed", copied, start, base, false},
		{"a head with another commit than what a side that reset removed", other, start, base, true},
		{"a head built on a side that rewound, with replays of two commits that it removed, which undo each other", tokens, rewound, revoked, false},
		{"a head built on a side that rewound, with a replay of a commit that it removed, whose change another removed commit undid", leaked, rewound, revoked, false},
		{"a head that merges a side that rewound with replays of two commits that it removed, which undo each other", mergedTokens, rewound, revoked, false},
		{"a head that replays a side that rewound next to a replay of a commit that it removed", replayedToken, rewound, revoked, false},
		{"a head with a replay of a commit that a side that rewound removed and replayed", leakedAgain, tokenAgain, revoked, true},
		{"a commit that a side that rewound contains", start, rewound, base, false},
		{"a head that contains the side and undoes its change", undone, side, base, true},
		{"a head that contains a side that never agreed", ahead, side, "", true},
		{"a head that doesn't contain a side that never agreed", base, side, "", false},
		{"no head, with a side that reset", "", start, base, true},
		{"no head, with a side that added a commit", "", side, base, false},
		{"no side, with a head that shares no commit with base", lone, "", base, true},
		{"no side, with a head that shares commits with base", other, "", base, false},
	} {
		t.Run(c.name, func(t *testing.T) {
			if got, err := repo.Keeps(t.Context(), c.head, c.side, c.base); err != nil || got != c.want {
				t.Errorf("Keeps(%.7s, %.7s, %.7s) = %t, %v; want %t", c.head, c.side, c.base, got, err, c.want)
			}
		})
	}

	t.Run("a commit that the repository doesn't have", func(t *testing.T) {
		if got, err := repo.Keeps(t.Context(), side, start, strings.Repeat("1", 40)); err == nil {
			t.Errorf("Keeps with a missing base = %t, want an error", got)
		}
	})

	t.Run("a union attribute in the head's tree", func(t *testing.T) {
		repo, err := (&git.Git{}).Open(t.Context(), filepath.Join(t.TempDir(), "app.git"))
		if err != nil {
			t.Fatal(err)
		}
		if err := repo.Fetch(t.Context(), srv.Remote("app"), branches...); err != nil {
			t.Fatal(err)
		}
		// attr.tree makes git read attributes from the head's tree, as some
		// versions do from HEAD in a bare repository.
		config := filepath.Join(repo.Dir, "config")
		b, err := os.ReadFile(config)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(config, append(b, "[attr]\n\ttree = "+union+"\n"...), 0o644); err != nil {
			t.Fatal(err)
		}
		if got, err := repo.Keeps(t.Context(), union, cut, base); err != nil || got {
			t.Errorf("Keeps = %t, %v; want false", got, err)
		}
	})
}

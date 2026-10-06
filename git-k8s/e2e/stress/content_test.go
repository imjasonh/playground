package main

import (
	"maps"
	"strings"
	"testing"
)

// TestBranchCommits checks, for each kind of branch, that its developer's
// first push has the files that main has once the branch lands, except for
// what a check or the developer fixes, and that only the high-risk kinds are
// high risk.
func TestBranchCommits(t *testing.T) {
	const sum = "example.com/greet v1.0.0 h1:a=\nexample.com/greet v1.0.0/go.mod h1:b=\n"
	const src, test = "feat/f007/f007.go", "feat/f007/f007_test.go"
	for _, kind := range []string{kindClean, kindUnformatted, kindFailing, kindConflict, kindBigRisk, kindModRisk, kindMulti} {
		t.Run(kind, func(t *testing.T) {
			b := branchPlan{Repo: "app", Name: "c/f007", ID: "f007", Kind: kind}
			if kind == kindConflict {
				b.Pair = 2
			}
			commits := branchCommits(b, sum)
			want := 1
			if kind == kindMulti {
				want = 3
			}
			if len(commits) != want {
				t.Errorf("%d commits, want %d", len(commits), want)
			}
			pushed := map[string]string{}
			for _, c := range commits {
				if c.message == "" {
					t.Error("a commit has no message")
				}
				maps.Copy(pushed, c.files)
			}
			for path, want := range expectedFiles(b) {
				got, ok := pushed[path]
				switch {
				case !ok:
					t.Errorf("the developer doesn't push %s", path)
				case kind == kindUnformatted && path == src:
					if got == want || gofmt(got) != want {
						t.Errorf("%s isn't a file that gofmt formats into main's:\n%s", path, got)
					}
				case kind == kindFailing && path == test:
					if got == want {
						t.Errorf("%s is already the fixed test", path)
					}
				case got != want:
					t.Errorf("%s = %q, want %q", path, got, want)
				}
			}
			lines := 0
			for path, content := range pushed {
				if path != "go.sum" {
					lines += strings.Count(content, "\n")
				}
			}
			switch kind {
			case kindBigRisk:
				if lines <= 200 {
					t.Errorf("the change has %d lines, not more than check-risk's -max-lines of 200", lines)
				}
			case kindModRisk:
				if !strings.Contains(pushed["go.mod"], "require example.com/greet v1.0.0") || pushed["go.sum"] != sum {
					t.Errorf("go.mod = %q and go.sum = %q, want a requirement of example.com/greet", pushed["go.mod"], pushed["go.sum"])
				}
			default:
				if lines > 200 {
					t.Errorf("the change has %d lines, which check-risk rates high", lines)
				}
			}
			if kind == kindConflict {
				if got, want := pushed[conflictFile(2)], conflictSource(2, "c/f007"); got != want {
					t.Errorf("%s = %q, want %q", conflictFile(2), got, want)
				}
			}
		})
	}
}

// TestBaseFiles checks that main starts formatted, since verification
// runs gofmt -l on main.
func TestBaseFiles(t *testing.T) {
	for path, src := range baseFiles() {
		if strings.HasSuffix(path, ".go") && gofmt(src) != src {
			t.Errorf("%s isn't formatted", path)
		}
	}
}

func TestFeatureNumber(t *testing.T) {
	for id, want := range map[string]int{"f007": 7, "f120": 120, "w00": 0} {
		if got := featureNumber(id); got != want {
			t.Errorf("featureNumber(%q) = %d, want %d", id, got, want)
		}
	}
}

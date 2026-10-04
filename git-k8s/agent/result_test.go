package agent

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"net/http"
	"net/http/httptest"
	"net/url"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

func TestCleansText(t *testing.T) {
	for _, tc := range []struct {
		in      string
		n       int
		oneLine bool
		want    string
	}{
		{"two\nlines\t here ", 200, true, "two lines here"},
		{"keeps\nlines\tand tabs\x1b[31m\r\n", 200, false, "keeps\nlines\tand tabs[31m"},
		{"héllo wörld", 8, true, "héllo..."},
		{"bad \xff byte", 200, true, "bad byte"},
	} {
		if got := clean(tc.in, tc.n, tc.oneLine); got != tc.want {
			t.Errorf("clean(%q, %d, %t) = %q, want %q", tc.in, tc.n, tc.oneLine, got, tc.want)
		}
	}
}

func TestChecksPaths(t *testing.T) {
	for _, path := range []string{"a.txt", "dir/b.txt", ".github/ci.yml", ".gitignore", "a/.gitx/b", "dir/file with spaces"} {
		if err := checkPath(path); err != nil {
			t.Errorf("checkPath(%q) = %v", path, err)
		}
	}
	for _, path := range []string{"", "/abs", "a//b", "a/", "./a", "a/../b", ".git", "x/.Git/config", "a\x00b", "a\nb", "\xff", strings.Repeat("a", maxPath+1)} {
		if err := checkPath(path); err == nil {
			t.Errorf("checkPath(%.40q) = nil, want an error", path)
		}
	}
}

func TestChecksFiles(t *testing.T) {
	many := make([]File, maxFiles+1)
	for i := range many {
		many[i] = File{Path: strconv.Itoa(i), Mode: "100644"}
	}
	for _, tc := range []struct {
		files []File
		want  string
	}{
		{many, "more than 1000"},
		{[]File{{Path: "a", Mode: "100644"}, {Path: "a", Deleted: true}}, `it changes "a" twice`},
		{[]File{{Path: "a", Deleted: true, Content: []byte("x")}}, "but also gives it content"},
		{[]File{{Path: "a", Mode: "040000"}}, `the mode "040000"`},
		{[]File{{Path: "a", Mode: "100644", Content: make([]byte, maxFileBytes+1)}}, "more than 8 MiB"},
	} {
		if err := checkFiles(tc.files); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("checkFiles = %v, want an error with %q", err, tc.want)
		}
	}
}

func TestAppliesFiles(t *testing.T) {
	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "repo"))
	if err != nil {
		t.Fatal(err)
	}
	const empty = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
	start, err := ApplyFiles(ctx, repo, empty, []File{
		{Path: "d/f.txt", Mode: "100644", Content: []byte("f\n")},
		{Path: "x", Mode: "100644", Content: []byte("x\n")},
		{Path: "keep", Mode: "100644", Content: []byte("keep\n")},
	})
	if err != nil {
		t.Fatal(err)
	}
	tree, err := ApplyFiles(ctx, repo, start, []File{
		{Path: "d", Mode: "100644", Content: []byte("now a file\n")},
		{Path: "d/f.txt", Deleted: true},
		{Path: "x", Deleted: true},
		{Path: "x/y", Mode: "100755", Content: []byte("y\n")},
		{Path: "missing", Deleted: true},
	})
	if err != nil {
		t.Fatal(err)
	}
	entries, err := repo.LsTree(ctx, tree)
	if err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, e := range entries {
		content, err := repo.ReadBlob(ctx, e.SHA)
		if err != nil {
			t.Fatal(err)
		}
		got = append(got, e.Mode+" "+e.Path+" "+strings.TrimSpace(string(content)))
	}
	if want := "100644 d now a file|100644 keep keep|100755 x/y y"; strings.Join(got, "|") != want {
		t.Errorf("tree = %q, want %q", strings.Join(got, "|"), want)
	}

	if same, err := ApplyFiles(ctx, repo, start, nil); err != nil || same != start {
		t.Errorf("ApplyFiles without files = %s, %v; want the same tree", same, err)
	}
	if _, err := ApplyFiles(ctx, repo, start, []File{{Path: ".git/config", Mode: "100644"}}); err == nil || !strings.Contains(err.Error(), "invalid path") {
		t.Errorf("ApplyFiles with a .git path = %v, want an error", err)
	}
}

// serveOn starts a server for the test, and returns a Runner that fetches
// from it and the server's host.
func serveOn(t *testing.T, h http.HandlerFunc) (*Runner, string) {
	hs := httptest.NewServer(h)
	t.Cleanup(hs.Close)
	u, err := url.Parse(hs.URL)
	if err != nil {
		t.Fatal(err)
	}
	port, err := strconv.Atoi(u.Port())
	if err != nil {
		t.Fatal(err)
	}
	return &Runner{port: port}, u.Hostname()
}

func TestFetchLimitsResults(t *testing.T) {
	r, host := serveOn(t, func(w http.ResponseWriter, _ *http.Request) { w.Write(make([]byte, maxResult+1)) })
	if _, err := r.fetch(t.Context(), host, "uid"); !errors.Is(err, errTooBig) {
		t.Errorf("fetch = %v, want errTooBig", err)
	}

	r, host = serveOn(t, func(w http.ResponseWriter, req *http.Request) {
		if req.URL.Path == "/result" {
			http.Redirect(w, req, "/elsewhere", http.StatusFound)
		}
	})
	if _, err := r.fetch(t.Context(), host, "uid"); err == nil || !strings.Contains(err.Error(), "302 Found") {
		t.Errorf("fetch = %v, want the redirect as an error", err)
	}
}

func TestFetchResult(t *testing.T) {
	body := []byte(`{"updates":[]}`)
	sum := sha256.Sum256(body)
	digest := "sha256:" + hex.EncodeToString(sum[:])
	r, host := serveOn(t, func(w http.ResponseWriter, req *http.Request) {
		if req.Header.Get("Authorization") != "Bearer uid" {
			http.Error(w, "wrong UID", http.StatusUnauthorized)
			return
		}
		w.Write(body)
	})
	ctx := t.Context()
	if got, err := FetchResult(ctx, host, r.port, "uid", digest); err != nil || string(got) != string(body) {
		t.Errorf("FetchResult = %q, %v; want %q", got, err, body)
	}
	if _, err := FetchResult(ctx, host, r.port, "other", digest); err == nil || errors.Is(err, ErrInvalidResult) {
		t.Errorf("FetchResult with another UID = %v, want an error that fetching again can fix", err)
	}
	for _, d := range []string{"sha256:" + strings.Repeat("0", 64), "done"} {
		if _, err := FetchResult(ctx, host, r.port, "uid", d); !errors.Is(err, ErrInvalidResult) {
			t.Errorf("FetchResult with digest %q = %v, want ErrInvalidResult", d, err)
		}
	}

	r, host = serveOn(t, func(w http.ResponseWriter, _ *http.Request) { w.Write(make([]byte, maxResult+1)) })
	if _, err := FetchResult(ctx, host, r.port, "uid", digest); !errors.Is(err, ErrInvalidResult) {
		t.Errorf("FetchResult of a large result = %v, want ErrInvalidResult", err)
	}
}

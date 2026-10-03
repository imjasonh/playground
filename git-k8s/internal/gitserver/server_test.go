package gitserver_test

import (
	"net/http"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestCloneAndPush(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "repo")
	w.Write("README.md", "hello\n")
	first := w.Commit("first")
	w.Push("main")

	other := srv.NewWork(t, "repo")
	if got := other.Fetch("main"); got != first {
		t.Errorf("fetched %s, want %s", got, first)
	}
	if got := other.Show(first, "README.md"); got != "hello" {
		t.Errorf("README.md = %q", got)
	}
}

func TestRequiresCredentials(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	resp, err := http.Get(srv.URL + "/repo.git/info/refs?service=git-upload-pack")
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusUnauthorized {
		t.Errorf("status = %d, want 401", resp.StatusCode)
	}
}

func TestRejectsBadPaths(t *testing.T) {
	srv := gittest.NewServer(t, "")
	for _, path := range []string{"/../etc.git/info/refs", "/repo/info/refs", "/repo.git/objects/info/packs"} {
		resp, err := http.Get(srv.URL + path + "?service=git-upload-pack")
		if err != nil {
			t.Fatal(err)
		}
		resp.Body.Close()
		if resp.StatusCode != http.StatusNotFound {
			t.Errorf("GET %s: status = %d, want 404", path, resp.StatusCode)
		}
	}
}

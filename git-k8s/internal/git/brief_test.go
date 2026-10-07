package git_test

import (
	"errors"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// git prints each line of the body of a server's error response after
// "remote: ", even a line that looks like git's own message, so Brief leaves
// the body out.
func TestBriefLeavesOutWhatTheServerSent(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		http.Error(w, "internal-only: db_password=hunter2\nfatal: not git's", http.StatusInternalServerError)
	}))
	defer hs.Close()
	_, err := (&git.Git{}).LsRemote(t.Context(), git.Remote{URL: hs.URL + "/app.git"})
	if err == nil {
		t.Fatal("ls-remote succeeded against a server that fails every request")
	}
	full := err.Error()
	want := strings.Replace(full, "remote: internal-only: db_password=hunter2\nremote: fatal: not git's\n", "", 1)
	if got := git.Brief(err).Error(); got != want || want == full {
		t.Errorf("Brief(%q) = %q, want %q", full, got, want)
	}
}

func TestBriefKeepsTheErrorTree(t *testing.T) {
	sentinel := errors.New("not synced")
	fetch := &git.Error{Command: "fetch", Code: 128, Stderr: "remote: Repository not found.\nhint: a hint\nerror: one\nfatal: two"}
	brief := git.Brief(fmt.Errorf("%w: fetching: %w", sentinel, fetch))
	if want := "not synced: fetching: git fetch: exit status 128: error: one\nfatal: two"; brief.Error() != want {
		t.Errorf("Brief = %q, want %q", brief, want)
	}
	if !errors.Is(brief, sentinel) || !errors.Is(brief, fetch) {
		t.Errorf("Brief's error %q doesn't wrap the original's tree", brief)
	}
	push := &git.Error{Command: "push", Code: 128, Stderr: "remote: Permission denied."}
	if got, want := git.Brief(push).Error(), "git push: exit status 128"; got != want {
		t.Errorf("Brief = %q, want %q", got, want)
	}

	for _, err := range []error{
		nil,
		errors.New("remote: not from git"),
		&git.Error{Command: "push", Code: 1, Stderr: "error: failed to push some refs"},
	} {
		if got := git.Brief(err); got != err {
			t.Errorf("Brief(%v) = %v, want the same error", err, got)
		}
	}
}

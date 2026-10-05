package git_test

import (
	"bytes"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"golang.org/x/sys/unix"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

// A process that a git command leaves behind becomes a child of the nearest
// subreaper, which in a container is PID 1, the Go program that ran the
// command and never waits for it. The test becomes a subreaper to stand in
// for PID 1.
func TestFetchLeavesNoProcesses(t *testing.T) {
	if err := unix.Prctl(unix.PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0); err != nil {
		t.Skipf("can't become a subreaper: %v", err)
	}
	t.Cleanup(func() { unix.Prctl(unix.PR_SET_CHILD_SUBREAPER, 0, 0, 0, 0) })
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Commit("first")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	for _, pid := range children(t) {
		t.Errorf("git fetch left process %d behind", pid)
		var status unix.WaitStatus
		unix.Wait4(pid, &status, 0, nil)
	}
}

// children returns the processes whose parent is the test's process. The
// commands that the test started have exited, so these are processes that
// the commands left behind.
func children(t *testing.T) []int {
	t.Helper()
	entries, err := os.ReadDir("/proc")
	if err != nil {
		t.Fatal(err)
	}
	self := strconv.Itoa(os.Getpid())
	var pids []int
	for _, e := range entries {
		pid, err := strconv.Atoi(e.Name())
		if err != nil {
			continue
		}
		stat, err := os.ReadFile(filepath.Join("/proc", e.Name(), "stat"))
		if err != nil {
			continue
		}
		// The parent's PID is the second field after the command name,
		// which can contain spaces and ends at the last ")".
		fields := strings.Fields(string(stat[bytes.LastIndexByte(stat, ')')+1:]))
		if len(fields) > 1 && fields[1] == self {
			pids = append(pids, pid)
		}
	}
	return pids
}

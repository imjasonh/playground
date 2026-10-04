package git

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"
)

// A command whose context ends gets SIGTERM, on which git removes its lock
// files, so a timeout or a cancelled request doesn't leave a ref locked.
func TestCancelRemovesLocks(t *testing.T) {
	g := &Git{}
	r, err := g.Open(t.Context(), filepath.Join(t.TempDir(), "repo.git"))
	if err != nil {
		t.Fatal(err)
	}
	blob, err := g.run(t.Context(), r.Dir, []string{"hash-object", "-w", "--stdin"}, opts{stdin: []byte("x\n")})
	if err != nil {
		t.Fatal(err)
	}
	// git gets pipes that are files as they are, so the command ends when
	// git exits, without waiting for copies to and from the pipes.
	stdin, toGit, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	fromGit, stdout, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	for _, f := range []*os.File{stdin, toGit, fromGit, stdout} {
		t.Cleanup(func() { f.Close() })
	}
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() {
		_, err := g.run(ctx, r.Dir, []string{"update-ref", "--stdin"}, opts{in: stdin, out: stdout})
		done <- err
	}()

	// prepare locks the transaction's refs until a commit or an abort.
	fmt.Fprintf(toGit, "start\ncreate refs/test/x %s\nprepare\n", strings.TrimSpace(string(blob)))
	lines := bufio.NewReader(fromGit)
	for _, want := range []string{"start: ok\n", "prepare: ok\n"} {
		if got, err := lines.ReadString('\n'); got != want {
			t.Fatalf("git said %q, %v; want %q", got, err, want)
		}
	}
	lock := filepath.Join(r.Dir, "refs", "test", "x.lock")
	if _, err := os.Stat(lock); err != nil {
		t.Fatalf("git doesn't hold the lock: %v", err)
	}
	cancel()
	if err := <-done; !errors.Is(err, context.Canceled) {
		t.Errorf("err = %v, want context.Canceled", err)
	}
	if _, err := os.Stat(lock); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("the lock is still there: %v", err)
	}
}

// A command that runs past its timeout stops with the commands that it
// started, as maintenance does with its repack, so none of them outlives
// the timeout.
func TestTimeoutStopsWhatGitStarted(t *testing.T) {
	if runtime.GOOS != "linux" {
		t.Skip("reads /proc")
	}
	dir := t.TempDir()
	pidFile := filepath.Join(dir, "pid")
	bin := filepath.Join(dir, "git")
	script := "#!/bin/sh\nsleep 600 &\necho $! > " + pidFile + "\nwait\n"
	if err := os.WriteFile(bin, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	g := &Git{Bin: bin, Timeout: 500 * time.Millisecond}
	start := time.Now()
	if _, err := g.run(t.Context(), "", []string{"maintenance"}, opts{}); !errors.Is(err, context.DeadlineExceeded) {
		t.Fatalf("err = %v, want context.DeadlineExceeded", err)
	}
	if d := time.Since(start); d >= stopDelay {
		t.Errorf("the command took %v, past its timeout and stopDelay", d)
	}
	data, err := os.ReadFile(pidFile)
	if err != nil {
		t.Fatalf("the fake git didn't start its child: %v", err)
	}
	pid, err := strconv.Atoi(strings.TrimSpace(string(data)))
	if err != nil {
		t.Fatal(err)
	}
	for deadline := time.Now().Add(5 * time.Second); ; time.Sleep(10 * time.Millisecond) {
		stat, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", pid))
		if err != nil || strings.Fields(string(stat))[2] == "Z" {
			return
		}
		if time.Now().After(deadline) {
			_ = syscall.Kill(pid, syscall.SIGKILL)
			t.Fatalf("the command's child %d still runs: %s", pid, stat)
		}
	}
}

// An error names git's command, not an option that comes before it, as
// --attr-source comes before merge-tree in Keeps.
func TestErrorNamesTheCommandAfterItsOptions(t *testing.T) {
	g := &Git{Bin: filepath.Join(t.TempDir(), "missing")}
	_, err := g.run(t.Context(), t.TempDir(), []string{"--attr-source=HEAD", "merge-tree"}, opts{})
	if err == nil || !strings.HasPrefix(err.Error(), "git merge-tree: ") {
		t.Errorf("err = %v, want an error that starts with %q", err, "git merge-tree: ")
	}
}

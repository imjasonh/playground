package git

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
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

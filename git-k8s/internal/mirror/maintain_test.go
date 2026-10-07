package mirror

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

// maintainInBackground runs w's Maintain until the test ends.
func (w *world) maintainInBackground() {
	done := make(chan struct{})
	go func() {
		defer close(done)
		w.m.Maintain(w.t.Context())
	}()
	w.t.Cleanup(func() { <-done })
}

// maintenance reports whether w's copy waits for Maintain, whether
// Maintain is maintaining it, and when Maintain may maintain it again
// after a failure.
func (w *world) maintenance() (queued, running bool, after time.Time) {
	e := w.m.entry(w.repo)
	w.m.mu.Lock()
	defer w.m.mu.Unlock()
	return e.queued, w.m.maintaining == e, e.maintainAfter
}

// maintenanceScript makes w's git run through a script in a new directory,
// and returns the directory. The script adds a line to the directory's
// file runs for each git maintenance. While the directory has a file named
// fail, the script fails each one, and while it has a file named hang, each
// one hangs.
func maintenanceScript(t *testing.T, w *world) string {
	t.Helper()
	dir := t.TempDir()
	script := `#!/bin/sh
dir=$(dirname "$0")
for a in "$@"; do
	if [ "$a" = maintenance ]; then
		echo >>"$dir/runs"
		if [ -e "$dir/fail" ]; then
			echo "fatal: simulated failure" >&2
			exit 128
		fi
		if [ -e "$dir/hang" ]; then
			exec sleep 600
		fi
	fi
done
exec git "$@"
`
	if err := os.WriteFile(filepath.Join(dir, "git"), []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	w.m.Git.Bin = filepath.Join(dir, "git")
	return dir
}

// runs counts the git maintenance commands that the script in dir ran.
func runs(t *testing.T, dir string) int {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(dir, "runs"))
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		t.Fatal(err)
	}
	return strings.Count(string(b), "\n")
}

// touch creates the empty file name in dir.
func touch(t *testing.T, dir, name string) {
	t.Helper()
	if err := os.WriteFile(filepath.Join(dir, name), nil, 0o644); err != nil {
		t.Fatal(err)
	}
}

// waitFor waits up to 30 seconds for cond.
func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	for start := time.Now(); !cond(); time.Sleep(10 * time.Millisecond) {
		if time.Since(start) > 30*time.Second {
			t.Fatalf("waited 30s for %s", what)
		}
	}
}

// within fails the test if f returns an error or takes longer than d.
func within(t *testing.T, d time.Duration, what string, f func() error) {
	t.Helper()
	done := make(chan error, 1)
	go func() { done <- f() }()
	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("%s: %v", what, err)
		}
	case <-time.After(d):
		t.Fatalf("%s took longer than %v", what, d)
	}
}

// hangMaintenance makes w's maintenance hang, syncs, and waits for Maintain
// to start maintaining w's copy. It returns the script's directory.
func hangMaintenance(t *testing.T, w *world) string {
	t.Helper()
	dir := maintenanceScript(t, w)
	touch(t, dir, "hang")
	w.maintainInBackground()
	w.sync(SyncOptions{})
	waitFor(t, "maintenance to start", func() bool {
		_, running, _ := w.maintenance()
		return running
	})
	return dir
}

// Fetches and pushes don't start git's maintenance, which would hold them
// up, and Sync only queues the copy for Maintain. Maintain packs the copy
// when it needs that, even after a killed maintenance left its lock, which
// makes maintenance skip the copy without an error.
func TestMaintainPacksCopy(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.sync(SyncOptions{})
	config := func(args ...string) string {
		t.Helper()
		return w.work.Git(append([]string{"--git-dir=" + w.copyDir(), "config"}, args...)...)
	}
	for key, want := range map[string]string{"maintenance.auto": "false", "receive.autogc": "false"} {
		if got := config(key); got != want {
			t.Errorf("the copy has %s = %q, want %q", key, got, want)
		}
	}

	// With gc.auto at 1, maintenance packs the copy once objects/17/ holds
	// two loose objects, and the fetch leaves every object loose.
	config("gc.auto", "1")
	config("fetch.unpackLimit", "1000000")
	w.work.Git("checkout", "--quiet", "--detach", base)
	for i := range 2000 {
		w.work.Write(fmt.Sprintf("many/%d.txt", i), fmt.Sprintf("file %d\n", i))
	}
	many := w.work.Commit("many")
	w.pushExternal("main", many)
	lock := filepath.Join(w.copyDir(), "objects", "maintenance.lock")
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	old := time.Now().Add(-w.m.maintenanceGit().MaxDuration() - 2*time.Minute)
	if err := os.Chtimes(lock, old, old); err != nil {
		t.Fatal(err)
	}

	if rep := w.sync(SyncOptions{Fetch: true}); rep.Heads["main"] != many {
		t.Fatalf("Report.Heads = %v; want main at %.7s", rep.Heads, many)
	}
	under17 := 0
	for line := range strings.SplitSeq(w.work.Git("--git-dir="+w.copyDir(), "rev-list", "--objects", "--all"), "\n") {
		if strings.HasPrefix(line, "17") {
			under17++
		}
	}
	if under17 < 2 {
		t.Fatalf("only %d of the fetched objects go under objects/17/, too few to need maintenance", under17)
	}
	if got := w.work.Git("--git-dir="+w.copyDir(), "count-objects"); strings.HasPrefix(got, "0 objects,") {
		t.Errorf("after Sync, git count-objects = %q, want the fetched objects loose", got)
	}
	if queued, _, _ := w.maintenance(); !queued {
		t.Fatal("after Sync, the copy doesn't wait for Maintain")
	}

	if !w.m.maintainNext(t.Context()) {
		t.Fatal("maintainNext = false, want true")
	}
	if got := w.work.Git("--git-dir="+w.copyDir(), "count-objects"); !strings.HasPrefix(got, "0 objects,") {
		t.Errorf("after Maintain, git count-objects = %q, want no loose objects", got)
	}
	for _, path := range []string{lock, filepath.Join(w.copyDir(), "gc.pid")} {
		if _, err := os.Stat(path); !errors.Is(err, os.ErrNotExist) {
			t.Errorf("after Maintain, %s is there: %v", filepath.Base(path), err)
		}
	}
}

// TestSyncDoesntWaitForMaintenance makes maintenance hang. The copy's
// syncs, fetches, and pushes go on beside it.
func TestSyncDoesntWaitForMaintenance(t *testing.T) {
	w := newWorld(t)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	dir := hangMaintenance(t, w)

	theirs, feature := w.commit(base, "theirs"), w.commit(base, "feature")
	w.pushExternal("main", theirs)
	w.pushCopy("feature", feature)
	var rep *Report
	within(t, time.Minute, "Sync", func() (err error) {
		rep, err = w.trySync(SyncOptions{Fetch: true, Push: true})
		return err
	})
	want := map[string]string{"feature": feature, "main": theirs}
	wantHeads(t, "Report.Heads", rep.Heads, want)
	wantHeads(t, "the external repository's branches", w.externalHeads(), want)
	if _, running, _ := w.maintenance(); !running || runs(t, dir) != 1 {
		t.Errorf("after the Sync, Maintain is maintaining the copy: %t, after %d git maintenance commands; want the first still running", running, runs(t, dir))
	}
}

// TestMaintainSkipsCopyAfterAFailure fails maintenance, or makes it run past
// MaintenanceTimeout, which is shorter than Git's Timeout. Either way,
// Maintain skips the copy until maintenanceRetry passes.
func TestMaintainSkipsCopyAfterAFailure(t *testing.T) {
	for _, file := range []string{"fail", "hang"} {
		t.Run(file, func(t *testing.T) {
			w := newWorld(t)
			w.pushExternal("main", w.commit("", "base"))
			dir := maintenanceScript(t, w)
			touch(t, dir, file)
			w.m.Git.Timeout = time.Hour
			w.m.MaintenanceTimeout = time.Second
			w.m.maintenanceRetry = 2 * time.Second

			w.sync(SyncOptions{})
			start := time.Now()
			w.m.maintainNext(t.Context())
			if d := time.Since(start); d > 30*time.Second {
				t.Errorf("the maintenance took %v, past MaintenanceTimeout", d)
			}
			failed := time.Now()
			w.sync(SyncOptions{})
			if queued, _, after := w.maintenance(); queued || after.IsZero() {
				t.Errorf("right after the maintenance failed, the copy waits for Maintain: %t, and Maintain may maintain it after %v; want it skipped for maintenanceRetry", queued, after)
			}

			time.Sleep(time.Until(failed.Add(w.m.maintenanceRetry)))
			w.sync(SyncOptions{})
			if queued, _, _ := w.maintenance(); !queued {
				t.Fatalf("%v after the maintenance failed, the copy doesn't wait for Maintain", w.m.maintenanceRetry)
			}
			w.m.maintainNext(t.Context())
			if got := runs(t, dir); got != 2 {
				t.Errorf("git maintenance ran %d times, want 2", got)
			}
		})
	}
}

// TestDeleteStopsMaintenance deletes a copy while its maintenance hangs.
// Delete waits for every other use of the copy, but stops the maintenance
// instead of waiting for it, and the stopped maintenance didn't fail.
func TestDeleteStopsMaintenance(t *testing.T) {
	w := newWorld(t)
	w.pushExternal("main", w.commit("", "base"))
	w.m.MaintenanceTimeout = time.Hour
	hangMaintenance(t, w)

	within(t, 30*time.Second, "Delete", func() error { return w.m.Delete(t.Context(), w.repo) })
	if _, err := os.Stat(w.copyDir()); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("after Delete, the copy is there: %v", err)
	}
	waitFor(t, "the maintenance to stop", func() bool {
		_, running, _ := w.maintenance()
		return !running
	})
	if _, _, after := w.maintenance(); !after.IsZero() {
		t.Errorf("after Delete stopped the maintenance, Maintain skips the copy until %v; want no failure", after)
	}
}

// TestNewURLStopsMaintenance moves a repository to a new URL while its
// copy's maintenance hangs. Adopting the URL waits for every other use of
// the copy, but stops the maintenance instead of waiting for it. The
// stopped maintenance didn't fail, so the sync queues the copy again.
func TestNewURLStopsMaintenance(t *testing.T) {
	ext := gittest.NewServer(t, "")
	w := newWorldAt(t, ext.NewWork(t, "app"), ext.Remote("app"), ext.Remote("app").URL)
	base := w.commit("", "base")
	w.pushExternal("main", base)
	w.m.MaintenanceTimeout = time.Hour
	dir := hangMaintenance(t, w)

	w.pushURL = ext.Remote("moved").URL
	w.pushExternal("main", base)
	w.remote, w.repo.Spec.URL = ext.Remote("moved"), ext.Remote("moved").URL
	within(t, 30*time.Second, "Sync with the new URL", func() error {
		_, err := w.trySync(SyncOptions{})
		return err
	})
	waitFor(t, "the maintenance to start again", func() bool { return runs(t, dir) == 2 })
}

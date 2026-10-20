package store

import (
	"context"
	"database/sql"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/benbjohnson/litestream"
)

func testConfig(t *testing.T, replicaDir string) Config {
	t.Helper()
	cfg := DefaultConfig()
	cfg.ReplicaURL = "file://" + replicaDir
	cfg.Dir = t.TempDir()
	cfg.PollInterval = 50 * time.Millisecond
	cfg.SyncInterval = 100 * time.Millisecond
	cfg.CompactionLevels = litestream.CompactionLevels{
		{Level: 0},
		{Level: 1, Interval: 200 * time.Millisecond},
		{Level: 2, Interval: time.Second},
	}
	cfg.SnapshotPlanLen = 0
	cfg.Logger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelWarn}))
	return cfg
}

func mustOpen(t *testing.T, cfg Config) *Store {
	t.Helper()
	s, err := Open(t.Context(), cfg)
	if err != nil {
		t.Fatalf("Open: %v", err)
	}
	return s
}

func mustWrite(t *testing.T, s *Store, query string, args ...any) {
	t.Helper()
	if err := s.Write(t.Context(), func(tx *sql.Tx) error {
		_, err := tx.Exec(query, args...)
		return err
	}); err != nil {
		t.Fatalf("Write(%q): %v", query, err)
	}
}

func count(t *testing.T, s *Store, table string) int {
	t.Helper()
	var n int
	if err := s.Read(t.Context(), func(db *sql.DB) error {
		return db.QueryRow("SELECT count(*) FROM " + table).Scan(&n)
	}); err != nil {
		t.Fatalf("count %s: %v", table, err)
	}
	return n
}

// rowCount is count for goroutines other than the test's.
func rowCount(ctx context.Context, s *Store, table string) (int, error) {
	var n int
	err := s.Read(ctx, func(db *sql.DB) error {
		return db.QueryRowContext(ctx, "SELECT count(*) FROM "+table).Scan(&n)
	})
	return n, err
}

// pauseOnce makes the next durable batch on s wait after its local commit,
// before its upload. paused is closed when the batch gets there. release
// lets it continue and can be called more than once.
func pauseOnce(s *Store) (paused <-chan struct{}, release func()) {
	p, r := make(chan struct{}), make(chan struct{})
	var once sync.Once
	s.hooks.beforeUpload = func() error {
		once.Do(func() {
			close(p)
			<-r
		})
		return nil
	}
	return p, sync.OnceFunc(func() { close(r) })
}

func integrity(t *testing.T, s *Store) {
	t.Helper()
	var res string
	if err := s.Read(t.Context(), func(db *sql.DB) error {
		return db.QueryRow("PRAGMA integrity_check").Scan(&res)
	}); err != nil || res != "ok" {
		t.Fatalf("integrity_check = %q, %v", res, err)
	}
}

func TestDurableWritesSurviveReopen(t *testing.T) {
	replica := t.TempDir()
	s := mustOpen(t, testConfig(t, replica))
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")
	for i := range 50 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (?)", fmt.Sprint(i))
	}
	// Simulate a crash: drop the instance without Close. Durable writes
	// must already be in the replica.
	s.closed.Store(true)

	s2 := mustOpen(t, testConfig(t, replica))
	defer s2.Close()
	if got := count(t, s2, "t"); got != 50 {
		t.Fatalf("rows after reopen = %d, want 50", got)
	}
	integrity(t, s2)
}

func TestConcurrentWritesShareBatches(t *testing.T) {
	s := mustOpen(t, testConfig(t, t.TempDir()))
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")

	var wg sync.WaitGroup
	for i := range 200 {
		wg.Go(func() {
			if err := s.Write(t.Context(), func(tx *sql.Tx) error {
				_, err := tx.Exec("INSERT INTO t (v) VALUES (?)", i)
				return err
			}); err != nil {
				t.Errorf("write %d: %v", i, err)
			}
		})
	}
	wg.Wait()
	if got := count(t, s, "t"); got != 200 {
		t.Fatalf("rows = %d, want 200", got)
	}
	if st := s.Stats(t.Context()); st.Batches >= 200 {
		t.Errorf("batches = %d, want fewer than 200 writes", st.Batches)
	}
}

func TestFailedWriteRollsBackOnlyItself(t *testing.T) {
	s := mustOpen(t, testConfig(t, t.TempDir()))
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT NOT NULL)")

	var wg sync.WaitGroup
	errs := make([]error, 20)
	for i := range errs {
		wg.Go(func() {
			errs[i] = s.Write(t.Context(), func(tx *sql.Tx) error {
				if i%2 == 1 {
					_, err := tx.Exec("INSERT INTO t (v) VALUES (NULL)")
					return err
				}
				_, err := tx.Exec("INSERT INTO t (v) VALUES (?)", i)
				return err
			})
		})
	}
	wg.Wait()
	for i, err := range errs {
		if (err != nil) != (i%2 == 1) {
			t.Errorf("write %d: err = %v", i, err)
		}
	}
	if got := count(t, s, "t"); got != 10 {
		t.Fatalf("rows = %d, want 10", got)
	}
}

// Two instances on one replica, as during a Cloud Run deploy. Each write
// must land exactly once and the replica must stay consistent.
func TestOverlappingInstancesConflictAndRetry(t *testing.T) {
	replica := t.TempDir()
	a := mustOpen(t, testConfig(t, replica))
	mustWrite(t, a, "CREATE TABLE t (id INTEGER PRIMARY KEY, who TEXT)")
	b := mustOpen(t, testConfig(t, replica))

	var wg sync.WaitGroup
	for _, inst := range []struct {
		name string
		s    *Store
	}{{"a", a}, {"b", b}} {
		wg.Go(func() {
			for range 40 {
				if err := inst.s.Write(t.Context(), func(tx *sql.Tx) error {
					_, err := tx.Exec("INSERT INTO t (who) VALUES (?)", inst.name)
					return err
				}); err != nil {
					t.Errorf("%s write: %v", inst.name, err)
				}
			}
		})
	}
	wg.Wait()
	if a.Stats(t.Context()).Conflicts+b.Stats(t.Context()).Conflicts == 0 {
		t.Log("no conflicts happened; the instances never raced")
	}
	if err := a.Close(); err != nil {
		t.Fatalf("close a: %v", err)
	}
	if err := b.Close(); err != nil {
		t.Fatalf("close b: %v", err)
	}

	c := mustOpen(t, testConfig(t, replica))
	defer c.Close()
	if got := count(t, c, "t"); got != 80 {
		t.Fatalf("rows = %d, want 80", got)
	}
	integrity(t, c)
}

// A writer whose last upload is recent skips the conflict-check LIST, so the
// conditional create catches another instance's upload of its next TXID.
// The writer then reopens and reruns its write after the other instance's.
func TestFreshWriterLosesTheConditionalCreate(t *testing.T) {
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	// Without a poll, a doesn't learn of b's upload before its own.
	cfg.PollInterval = time.Hour
	a := mustOpen(t, cfg)
	defer a.Close()
	mustWrite(t, a, "CREATE TABLE t (id INTEGER PRIMARY KEY, who TEXT)")
	mustWrite(t, a, "INSERT INTO t (who) VALUES ('a')")

	b := mustOpen(t, testConfig(t, replica))
	mustWrite(t, b, "INSERT INTO t (who) VALUES ('b')")
	if err := b.Close(); err != nil {
		t.Fatalf("close b: %v", err)
	}

	// The VFS's sync loop can retry the upload before the store reopens, and
	// the conditional create rejects every attempt.
	before := a.Stats(t.Context()).Conflicts
	mustWrite(t, a, "INSERT INTO t (who) VALUES ('a')")
	if got := a.Stats(t.Context()).Conflicts - before; got < 1 {
		t.Fatalf("a's upload hit %d conditional-create conflicts, want at least 1", got)
	}

	c := mustOpen(t, testConfig(t, replica))
	defer c.Close()
	if got := count(t, c, "t"); got != 3 {
		t.Fatalf("rows = %d, want 3", got)
	}
	integrity(t, c)
}

// A durable write is in the replica before any read can see it.
func TestReadsWaitForUpload(t *testing.T) {
	s := mustOpen(t, testConfig(t, t.TempDir()))
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")

	paused, release := pauseOnce(s)
	defer release()
	written := make(chan error, 1)
	go func() {
		written <- s.Write(t.Context(), func(tx *sql.Tx) error {
			_, err := tx.Exec("INSERT INTO t (v) VALUES ('x')")
			return err
		})
	}()
	<-paused

	type result struct {
		n   int
		err error
	}
	read := make(chan result, 1)
	go func() {
		n, err := rowCount(t.Context(), s, "t")
		read <- result{n, err}
	}()
	select {
	case r := <-read:
		t.Fatalf("a read returned %d rows, %v while the write was committed but not uploaded", r.n, r.err)
	case <-time.After(200 * time.Millisecond):
	}
	release()
	if err := <-written; err != nil {
		t.Fatalf("Write: %v", err)
	}
	if r := <-read; r.err != nil || r.n != 1 {
		t.Fatalf("read after the upload = %d rows, %v; want 1 row", r.n, r.err)
	}
}

// During a deploy, two instances write to one replica. The instance that
// loses the race for a TXID has already committed its write locally, under
// a row id that the winner's write took. Reads there must never see it.
func TestReadsNeverSeeALosingWrite(t *testing.T) {
	replica := t.TempDir()
	open := func() *Store {
		cfg := testConfig(t, replica)
		// b must not poll a's insert before it writes its own.
		cfg.PollInterval = time.Hour
		cfg.CompactionLevels = nil
		return mustOpen(t, cfg)
	}
	a := open()
	defer a.Close()
	mustWrite(t, a, "CREATE TABLE items (id INTEGER PRIMARY KEY, body TEXT)")
	b := open()
	defer b.Close()
	mustWrite(t, a, "INSERT INTO items (body) VALUES ('from a')")

	paused, release := pauseOnce(b)
	defer release()
	written := make(chan error, 1)
	go func() {
		written <- b.Write(t.Context(), func(tx *sql.Tx) error {
			_, err := tx.Exec("INSERT INTO items (body) VALUES ('from b')")
			return err
		})
	}()
	<-paused

	type result struct {
		body string
		err  error
	}
	read := make(chan result, 1)
	go func() {
		var r result
		r.err = b.Read(t.Context(), func(db *sql.DB) error {
			return db.QueryRow("SELECT body FROM items WHERE id = 1").Scan(&r.body)
		})
		read <- r
	}()
	select {
	case r := <-read:
		t.Fatalf("a read on b returned %q, %v while b's write was neither uploaded nor thrown away", r.body, r.err)
	case <-time.After(200 * time.Millisecond):
	}
	release()
	if err := <-written; err != nil {
		t.Fatalf("b's Write: %v", err)
	}
	if r := <-read; r.err != nil || r.body != "from a" {
		t.Fatalf("id 1 on b = %q, %v; want %q", r.body, r.err, "from a")
	}
	if b.Stats(t.Context()).Reopens == 0 {
		t.Error("b didn't reopen after its write lost")
	}
	if got := count(t, b, "items"); got != 2 {
		t.Fatalf("rows on b = %d, want 2", got)
	}
}

// An upload can fail for reasons other than a conflict. Reads must not see
// the failed write, and writes must work again once the replica does.
func TestFailedUploadIsDiscarded(t *testing.T) {
	if os.Geteuid() == 0 {
		t.Skip("root ignores the directory permission this test uses to fail uploads")
	}
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	cfg.CompactionLevels = nil
	s := mustOpen(t, cfg)
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")
	mustWrite(t, s, "INSERT INTO t (v) VALUES ('kept')")

	l0 := filepath.FromSlash(litestream.LTXLevelDir(replica, 0))
	if err := os.Chmod(l0, 0o555); err != nil {
		t.Fatal(err)
	}
	err := s.Write(t.Context(), func(tx *sql.Tx) error {
		_, err := tx.Exec("INSERT INTO t (v) VALUES ('lost')")
		return err
	})
	if chmodErr := os.Chmod(l0, 0o755); chmodErr != nil {
		t.Fatal(chmodErr)
	}
	if err == nil {
		t.Fatal("Write succeeded while L0 was read-only")
	}
	if got := count(t, s, "t"); got != 1 {
		t.Fatalf("rows after the failed upload = %d, want 1", got)
	}

	mustWrite(t, s, "INSERT INTO t (v) VALUES ('after')")
	s2 := mustOpen(t, testConfig(t, replica))
	defer s2.Close()
	if got := count(t, s2, "t"); got != 2 {
		t.Fatalf("rows in the replica = %d, want 2", got)
	}
	integrity(t, s2)
}

// If the store can't reopen the database after a failed upload, reads
// return ErrUnavailable instead of using a closed database, and the store
// opens it again when it can.
func TestUnavailableUntilReopenSucceeds(t *testing.T) {
	replica := t.TempDir()
	s := mustOpen(t, testConfig(t, replica))
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")

	errUpload, errOpen := errors.New("injected upload failure"), errors.New("injected open failure")
	var uploads, opens atomic.Int32
	s.hooks.beforeUpload = func() error {
		if uploads.Add(1) == 1 {
			return errUpload
		}
		return nil
	}
	s.hooks.beforeOpen = func() error {
		if opens.Add(1) <= 2 {
			return errOpen
		}
		return nil
	}
	insert := func(v string) error {
		return s.Write(t.Context(), func(tx *sql.Tx) error {
			_, err := tx.Exec("INSERT INTO t (v) VALUES (?)", v)
			return err
		})
	}

	if err := insert("a"); !errors.Is(err, errUpload) || !errors.Is(err, errOpen) {
		t.Fatalf("first Write = %v, want the upload and reopen failures", err)
	}
	if err := insert("b"); !errors.Is(err, errOpen) {
		t.Fatalf("second Write = %v, want %v", err, errOpen)
	}
	unavailable := 0
	for deadline := time.Now().Add(10 * time.Second); ; {
		_, err := rowCount(t.Context(), s, "t")
		if !errors.Is(err, ErrUnavailable) {
			if err != nil {
				t.Fatalf("read: %v", err)
			}
			break
		}
		unavailable++
		if time.Now().After(deadline) {
			t.Fatal("database still unavailable after 10 s")
		}
		time.Sleep(10 * time.Millisecond)
	}
	if unavailable == 0 {
		t.Error("no read returned ErrUnavailable")
	}
	if err := insert("c"); err != nil {
		t.Fatalf("Write after reopening: %v", err)
	}

	// Closing the old database retried the first upload, which landed, so
	// the replica has "a" and "c". This instance shows the same.
	s2 := mustOpen(t, testConfig(t, replica))
	defer s2.Close()
	if got, want := count(t, s, "t"), count(t, s2, "t"); got != want || want != 2 {
		t.Fatalf("rows here = %d, in the replica = %d; want 2 in both", got, want)
	}
}

func TestSnapshotShortensRestorePlan(t *testing.T) {
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	cfg.CompactionLevels = nil
	cfg.L0Retention = 50 * time.Millisecond
	s := mustOpen(t, cfg)
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v BLOB)")
	for range 30 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (randomblob(3000))")
	}
	plan, err := s.RestorePlan(t.Context())
	if err != nil {
		t.Fatal(err)
	}
	if len(plan) < 30 {
		t.Fatalf("plan has %d files before snapshot, want at least 30", len(plan))
	}

	if _, err := s.Snapshot(t.Context()); err != nil {
		t.Fatalf("Snapshot: %v", err)
	}
	if plan, _ = s.RestorePlan(t.Context()); len(plan) != 1 {
		t.Fatalf("plan has %d files after snapshot, want 1", len(plan))
	}

	// The writer keeps working after its page index moved to the snapshot.
	for range 5 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (randomblob(3000))")
	}
	integrity(t, s)

	// A second snapshot lets retention delete what the first one covered,
	// once the L0 files are older than L0Retention.
	time.Sleep(2 * cfg.L0Retention)
	res, err := s.Snapshot(t.Context())
	if err != nil {
		t.Fatalf("second Snapshot: %v", err)
	}
	if res.Deleted < 30 {
		t.Errorf("retention deleted %d files, want at least 30", res.Deleted)
	}
	if err := s.Close(); err != nil {
		t.Fatal(err)
	}

	s2 := mustOpen(t, cfg)
	defer s2.Close()
	if got := count(t, s2, "t"); got != 35 {
		t.Fatalf("rows = %d, want 35", got)
	}
	integrity(t, s2)
}

// Two snapshots in quick succession must not delete L0 files younger than
// L0Retention. A writer that skips the conflict-check LIST relies on another
// writer's file for its next TXID staying in place.
func TestRetentionKeepsRecentL0Files(t *testing.T) {
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	cfg.CompactionLevels = nil
	cfg.L0Retention = time.Hour
	s := mustOpen(t, cfg)
	defer s.Close()
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v BLOB)")
	for range 5 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (randomblob(3000))")
	}
	if _, err := s.Snapshot(t.Context()); err != nil {
		t.Fatalf("Snapshot: %v", err)
	}
	for range 5 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (randomblob(3000))")
	}
	before, err := s.listLevel(t.Context(), 0)
	if err != nil {
		t.Fatal(err)
	}

	res, err := s.Snapshot(t.Context())
	if err != nil {
		t.Fatalf("second Snapshot: %v", err)
	}
	if res.Deleted != 0 {
		t.Errorf("retention deleted %d files, want 0", res.Deleted)
	}
	after, err := s.listLevel(t.Context(), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(after) != len(before) {
		t.Fatalf("L0 has %d files after the second snapshot, want %d", len(after), len(before))
	}
}

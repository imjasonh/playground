package store

import (
	"database/sql"
	"fmt"
	"log/slog"
	"os"
	"sync"
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

func TestSnapshotShortensRestorePlan(t *testing.T) {
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	cfg.CompactionLevels = nil
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

	// A second snapshot lets retention delete what the first one covered.
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

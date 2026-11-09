package store

import (
	"context"
	"database/sql"
	"errors"
	"fmt"
	"log/slog"
	"net/http/httptest"
	"slices"
	"sync"
	"testing"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fakegcs"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
)

func testContext(t *testing.T) context.Context {
	return clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler))
}

func testConfig(t *testing.T, replica string) Config {
	cfg := DefaultConfig()
	cfg.ReplicaURL = replica
	cfg.Dir = t.TempDir()
	cfg.SnapshotMinEntries = 0
	cfg.MemoryLimit = "128MB"
	cfg.Threads = 1
	return cfg
}

func open(t *testing.T, cfg Config) *Store {
	t.Helper()
	s, err := Open(testContext(t), cfg)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { s.Close() })
	return s
}

func migrate(t *testing.T, s *Store) {
	t.Helper()
	if err := s.Write(testContext(t), func(tx *sql.Tx) error {
		_, err := tx.Exec(`
			CREATE TABLE IF NOT EXISTS items (id BIGINT PRIMARY KEY, body VARCHAR NOT NULL);
			CREATE SEQUENCE IF NOT EXISTS items_id;
		`)
		return err
	}); err != nil {
		t.Fatal(err)
	}
}

func insert(t *testing.T, s *Store, body string) int64 {
	t.Helper()
	var id int64
	if err := s.Write(testContext(t), func(tx *sql.Tx) error {
		return tx.QueryRow("INSERT INTO items VALUES (nextval('items_id'), ?) RETURNING id", body).Scan(&id)
	}); err != nil {
		t.Fatalf("insert %q: %v", body, err)
	}
	return id
}

func bodies(t *testing.T, s *Store) []string {
	t.Helper()
	var out []string
	if err := s.Read(testContext(t), func(q Querier) error {
		rows, err := q.QueryContext(testContext(t), "SELECT body FROM items ORDER BY id")
		if err != nil {
			return err
		}
		defer rows.Close()
		for rows.Next() {
			var b string
			if err := rows.Scan(&b); err != nil {
				return err
			}
			out = append(out, b)
		}
		return rows.Err()
	}); err != nil {
		t.Fatal(err)
	}
	return out
}

func replicaURL(t *testing.T) string { return "file://" + t.TempDir() }

func TestRestoreSeesAcknowledgedWrites(t *testing.T) {
	replica := replicaURL(t)
	s := open(t, testConfig(t, replica))
	migrate(t, s)
	for i := range 20 {
		insert(t, s, fmt.Sprint("row", i))
	}
	s.Close()

	r := open(t, testConfig(t, replica))
	got := bodies(t, r)
	if len(got) != 20 || got[0] != "row0" || got[19] != "row19" {
		t.Fatalf("restored %v", got)
	}
	st := r.Stats()
	if st.BaseSeq != 1 || st.Seq != 22 {
		t.Fatalf("restored to base %d, seq %d; want the empty base 1, the migration, and 20 inserts", st.BaseSeq, st.Seq)
	}
	// The restored instance keeps appending to the same log.
	insert(t, r, "after")
	r.Close()
	got = bodies(t, open(t, testConfig(t, replica)))
	if len(got) != 21 || got[20] != "after" {
		t.Fatalf("after a second restore: %v", got)
	}
}

func TestUpdatesAndDeletesReplay(t *testing.T) {
	replica := replicaURL(t)
	s := open(t, testConfig(t, replica))
	migrate(t, s)
	for i := range 10 {
		insert(t, s, fmt.Sprint(i))
	}
	err := s.Write(testContext(t), func(tx *sql.Tx) error {
		if _, err := tx.Exec("DELETE FROM items WHERE id % 3 = 0"); err != nil {
			return err
		}
		_, err := tx.Exec("UPDATE items SET body = body || '!' WHERE id % 2 = 0")
		return err
	})
	if err != nil {
		t.Fatal(err)
	}
	want := bodies(t, s)
	if _, err := s.Snapshot(testContext(t)); err != nil {
		t.Fatal(err)
	}
	err = s.Write(testContext(t), func(tx *sql.Tx) error {
		_, err := tx.Exec("DELETE FROM items WHERE id = 2")
		return err
	})
	if err != nil {
		t.Fatal(err)
	}
	want = slices.DeleteFunc(want, func(b string) bool { return b == "1!" })
	s.Close()
	if got := bodies(t, open(t, testConfig(t, replica))); !slices.Equal(got, want) {
		t.Fatalf("restored %v, want %v", got, want)
	}
}

func TestDurableReadDoesNotSeeOrWaitForUpload(t *testing.T) {
	s := open(t, testConfig(t, replicaURL(t)))
	migrate(t, s)
	insert(t, s, "first")

	uploading := make(chan struct{})
	release := make(chan struct{})
	s.hooks.beforeUpload = func() error {
		close(uploading)
		<-release
		return nil
	}
	done := make(chan error, 1)
	go func() {
		done <- s.Write(testContext(t), func(tx *sql.Tx) error {
			_, err := tx.Exec("INSERT INTO items VALUES (nextval('items_id'), 'second')")
			return err
		})
	}()
	<-uploading
	start := time.Now()
	if got := bodies(t, s); !slices.Equal(got, []string{"first"}) {
		t.Fatalf("read during upload saw %v", got)
	}
	if d := time.Since(start); d > time.Second {
		t.Fatalf("read waited %s for the upload", d)
	}
	close(release)
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	if got := bodies(t, s); !slices.Equal(got, []string{"first", "second"}) {
		t.Fatalf("read after upload saw %v", got)
	}
}

func TestFailedUploadDiscardsWrite(t *testing.T) {
	replica := replicaURL(t)
	s := open(t, testConfig(t, replica))
	migrate(t, s)
	insert(t, s, "kept")
	fail := true
	s.hooks.beforeUpload = func() error {
		if fail {
			return errors.New("upload failed")
		}
		return nil
	}
	if err := s.Write(testContext(t), func(tx *sql.Tx) error {
		_, err := tx.Exec("INSERT INTO items VALUES (nextval('items_id'), 'lost')")
		return err
	}); err == nil {
		t.Fatal("write succeeded although its upload failed")
	}
	if got := bodies(t, s); !slices.Equal(got, []string{"kept"}) {
		t.Fatalf("after a failed upload: %v", got)
	}
	fail = false
	insert(t, s, "next")
	s.Close()
	if got := bodies(t, open(t, testConfig(t, replica))); !slices.Equal(got, []string{"kept", "next"}) {
		t.Fatalf("restored %v", got)
	}
}

func TestFailingWriteLeavesBatchIntact(t *testing.T) {
	s := open(t, testConfig(t, replicaURL(t)))
	migrate(t, s)
	release := make(chan struct{})
	s.hooks.beforeUpload = func() error {
		<-release
		return nil
	}
	// The first write holds the committer in its upload so the rest queue
	// up and share one batch.
	var wg sync.WaitGroup
	wg.Go(func() { insert(t, s, "a") })
	time.Sleep(50 * time.Millisecond)
	errs := make([]error, 5)
	for i := range errs {
		wg.Go(func() {
			errs[i] = s.Write(testContext(t), func(tx *sql.Tx) error {
				if i == 2 {
					_, err := tx.Exec("INSERT INTO items VALUES (1, 'duplicate key')")
					return err
				}
				_, err := tx.Exec("INSERT INTO items VALUES (nextval('items_id'), ?)", fmt.Sprint("b", i))
				return err
			})
		})
	}
	time.Sleep(50 * time.Millisecond)
	close(release)
	wg.Wait()
	for i, err := range errs {
		if (err != nil) != (i == 2) {
			t.Errorf("write %d: %v", i, err)
		}
	}
	if got := bodies(t, s); len(got) != 5 {
		t.Fatalf("items %v, want a and four b's", got)
	}
}

func TestOverlappingInstancesBothLand(t *testing.T) {
	srv := httptest.NewServer(fakegcs.New(t.TempDir(), fakegcs.Latency{Put: 5 * time.Millisecond}))
	t.Cleanup(srv.Close)
	replica := "gs://bucket/db?endpoint=" + srv.URL
	a := open(t, testConfig(t, replica))
	migrate(t, a)
	b := open(t, testConfig(t, replica))

	var wg sync.WaitGroup
	var mu sync.Mutex
	ids := map[int64]string{}
	for _, inst := range []*Store{a, b} {
		for w := range 4 {
			wg.Go(func() {
				for i := range 10 {
					body := fmt.Sprintf("%p-%d-%d", inst, w, i)
					id := insert(t, inst, body)
					mu.Lock()
					if prev, dup := ids[id]; dup {
						t.Errorf("id %d acknowledged for %q and %q", id, prev, body)
					}
					ids[id] = body
					mu.Unlock()
				}
			})
		}
	}
	wg.Wait()
	if a.Stats().Conflicts+b.Stats().Conflicts == 0 {
		t.Log("no conflicts; the instances didn't race")
	}
	a.Close()
	b.Close()
	got := bodies(t, open(t, testConfig(t, replica)))
	if len(got) != len(ids) {
		t.Fatalf("restored %d items, acknowledged %d", len(got), len(ids))
	}
}

func TestSnapshotsBoundRestoreAndRetentionDeletes(t *testing.T) {
	replica := replicaURL(t)
	cfg := testConfig(t, replica)
	cfg.SnapshotMinEntries = 5
	cfg.SnapshotEntryCost = 1 << 30
	cfg.Retention = 0
	s := open(t, cfg)
	migrate(t, s)
	for i := range 23 {
		insert(t, s, fmt.Sprint(i))
	}
	st := s.Stats()
	if st.Snapshots < 3 {
		t.Fatalf("%d snapshots after 23 writes, want at least 3", st.Snapshots)
	}
	if st.Entries >= 5 {
		t.Fatalf("%d entries after the last base", st.Entries)
	}
	b, err := objstore.Open(t.Context(), replica)
	if err != nil {
		t.Fatal(err)
	}
	bases, _ := b.List(t.Context(), basePrefix, "")
	if len(bases) > 2 {
		t.Fatalf("retention kept %d bases, want the newest two", len(bases))
	}
	s.Close()
	r := open(t, testConfig(t, replica))
	if got := bodies(t, r); len(got) != 23 {
		t.Fatalf("restored %d items", len(got))
	}
	if e := r.Stats().LastRestore.Entries; e >= 5 {
		t.Fatalf("restore read %d entries", e)
	}
}

// TestLargeInsertGoesThroughWAL checks that an append big enough for
// DuckDB to write row groups straight into the main file by default stays
// in the WAL, so it ships as one log entry instead of forcing a new base.
func TestLargeInsertGoesThroughWAL(t *testing.T) {
	replica := replicaURL(t)
	s := open(t, testConfig(t, replica))
	migrate(t, s)
	before := s.Stats()
	if err := s.Write(testContext(t), func(tx *sql.Tx) error {
		_, err := tx.Exec("INSERT INTO items SELECT i, 'bulk' || i FROM range(1000, 301000) t(i)")
		return err
	}); err != nil {
		t.Fatal(err)
	}
	after := s.Stats()
	if after.BaseSeq != before.BaseSeq || after.Seq != before.Seq+1 {
		t.Fatalf("large insert moved base %d -> %d and seq %d -> %d; want the same base and one entry", before.BaseSeq, after.BaseSeq, before.Seq, after.Seq)
	}
	insert(t, s, "after bulk")
	s.Close()
	r := open(t, testConfig(t, replica))
	var n int64
	r.Read(testContext(t), func(q Querier) error {
		return q.QueryRowContext(testContext(t), "SELECT count(*) FROM items").Scan(&n)
	})
	if n != 300001 {
		t.Fatalf("restored %d items, want 300001", n)
	}
}

func TestNotDurableUploadsInBackground(t *testing.T) {
	replica := replicaURL(t)
	cfg := testConfig(t, replica)
	cfg.Durable = false
	cfg.SyncInterval = 20 * time.Millisecond
	s := open(t, cfg)
	migrate(t, s)
	insert(t, s, "x")
	deadline := time.Now().Add(5 * time.Second)
	for s.Stats().Seq < 2 && time.Now().Before(deadline) {
		time.Sleep(10 * time.Millisecond)
	}
	r := open(t, testConfig(t, replica))
	if got := bodies(t, r); !slices.Equal(got, []string{"x"}) {
		t.Fatalf("restored %v", got)
	}
}

func TestReadOnlyFollowsWritesAndBases(t *testing.T) {
	replica := replicaURL(t)
	w := open(t, testConfig(t, replica))
	migrate(t, w)
	insert(t, w, "one")

	cfg := testConfig(t, replica)
	cfg.ReadOnly = true
	cfg.PollInterval = 20 * time.Millisecond
	r := open(t, cfg)
	if err := r.Write(testContext(t), func(*sql.Tx) error { return nil }); !errors.Is(err, ErrReadOnly) {
		t.Fatalf("Write on read-only store: %v", err)
	}
	waitFor := func(want []string) {
		t.Helper()
		deadline := time.Now().Add(5 * time.Second)
		for {
			got := bodies(t, r)
			if slices.Equal(got, want) {
				return
			}
			if time.Now().After(deadline) {
				t.Fatalf("replica has %v, want %v", got, want)
			}
			select {
			case <-r.Refreshed():
			case <-time.After(50 * time.Millisecond):
			}
		}
	}
	waitFor([]string{"one"})
	insert(t, w, "two")
	waitFor([]string{"one", "two"})
	if _, err := w.Snapshot(testContext(t)); err != nil {
		t.Fatal(err)
	}
	insert(t, w, "three")
	waitFor([]string{"one", "two", "three"})
}

func TestStaleWriterCatchesUpAfterRetention(t *testing.T) {
	replica := replicaURL(t)
	cfg := testConfig(t, replica)
	cfg.Retention = 0
	a := open(t, cfg)
	migrate(t, a)
	insert(t, a, "a1")
	cfg.Dir = t.TempDir()
	b := open(t, cfg)

	// a moves on, snapshots twice, and retention deletes the entries b
	// would otherwise collide with.
	insert(t, a, "a2")
	a.Snapshot(testContext(t))
	insert(t, a, "a3")
	a.Snapshot(testContext(t))
	a.Close()

	// b hasn't confirmed its position for longer than half of Retention,
	// so it lists before publishing and catches up instead of writing an
	// entry that no restore would read.
	insert(t, b, "b1")
	b.Close()
	got := bodies(t, open(t, testConfig(t, replica)))
	if !slices.Equal(got, []string{"a1", "a2", "a3", "b1"}) {
		t.Fatalf("restored %v", got)
	}
}

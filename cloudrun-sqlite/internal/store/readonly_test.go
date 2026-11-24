package store

import (
	"database/sql"
	"errors"
	"io/fs"
	"maps"
	"path/filepath"
	"testing"
	"time"
)

func TestReadOnlyFollowsWriterAndNeverWrites(t *testing.T) {
	dir := t.TempDir()
	wcfg := testConfig(t, dir)
	wcfg.CompactionLevels = nil
	writer := mustOpen(t, wcfg)
	defer writer.Close()
	mustWrite(t, writer, "CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)")
	mustWrite(t, writer, "INSERT INTO t (v) VALUES ('a')")

	rcfg := testConfig(t, dir)
	rcfg.ReadOnly = true
	reader := mustOpen(t, rcfg)
	defer reader.Close()
	if got := count(t, reader, "t"); got != 1 {
		t.Fatalf("reader sees %d rows, want 1", got)
	}

	before := replicaFiles(t, dir)
	if err := reader.Write(t.Context(), func(tx *sql.Tx) error { return nil }); !errors.Is(err, ErrReadOnly) {
		t.Errorf("Write = %v, want ErrReadOnly", err)
	}
	if err := reader.Flush(t.Context()); !errors.Is(err, ErrReadOnly) {
		t.Errorf("Flush = %v, want ErrReadOnly", err)
	}
	if _, err := reader.Snapshot(t.Context()); !errors.Is(err, ErrReadOnly) {
		t.Errorf("Snapshot = %v, want ErrReadOnly", err)
	}
	// A statement that writes through Read must fail in SQLite itself,
	// even after asking the VFS to enable writes.
	if err := reader.Read(t.Context(), func(db *sql.DB) error {
		if _, err := db.Exec("INSERT INTO t (v) VALUES ('b')"); err == nil {
			t.Error("INSERT through Read succeeded")
		}
		db.Exec("PRAGMA litestream_write_enabled = 1")
		if _, err := db.Exec("INSERT INTO t (v) VALUES ('c')"); err == nil {
			t.Error("INSERT after PRAGMA litestream_write_enabled succeeded")
		}
		if _, err := db.Exec("CREATE TABLE u (x)"); err == nil {
			t.Error("CREATE TABLE through Read succeeded")
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	if after := replicaFiles(t, dir); !maps.Equal(before, after) {
		t.Fatalf("replica changed while only the reader ran:\nbefore %v\nafter  %v", before, after)
	}

	mustWrite(t, writer, "INSERT INTO t (v) VALUES ('d')")
	deadline := time.Now().Add(5 * time.Second)
	for count(t, reader, "t") != 2 {
		if time.Now().After(deadline) {
			t.Fatalf("reader never saw the writer's second row")
		}
		time.Sleep(20 * time.Millisecond)
	}
}

func TestReadOnlyOpenWaitsForWriter(t *testing.T) {
	dir := t.TempDir()
	rcfg := testConfig(t, dir)
	rcfg.ReadOnly = true
	opened := make(chan *Store, 1)
	go func() { opened <- mustOpen(t, rcfg) }()

	select {
	case s := <-opened:
		s.Close()
		t.Fatal("read-only Open returned before any database existed")
	case <-time.After(300 * time.Millisecond):
	}
	if files := replicaFiles(t, dir); len(files) != 0 {
		t.Fatalf("read-only Open wrote to the replica: %v", files)
	}

	writer := mustOpen(t, testConfig(t, dir))
	defer writer.Close()
	mustWrite(t, writer, "CREATE TABLE t (id INTEGER PRIMARY KEY)")

	select {
	case reader := <-opened:
		defer reader.Close()
		if got := count(t, reader, "t"); got != 0 {
			t.Fatalf("reader sees %d rows, want 0", got)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("read-only Open didn't return after the writer created the database")
	}
}

// replicaFiles maps each file under dir to its size.
func replicaFiles(t *testing.T, dir string) map[string]int64 {
	t.Helper()
	files := map[string]int64{}
	if err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return err
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(dir, path)
		files[rel] = info.Size()
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	return files
}

package store

import (
	"database/sql"
	"testing"
	"time"
)

// With auto_vacuum, a DELETE shrinks the database and writes only the pages
// it changes. Another instance that polls the replica must keep the pages
// the DELETE didn't write.
func TestShrinkIsVisibleToAnotherInstance(t *testing.T) {
	replica := t.TempDir()
	cfg := testConfig(t, replica)
	// An L1 file that compacts the DELETE with the files before it holds
	// every page, which would hide a reader that keeps only the DELETE's.
	cfg.CompactionLevels[1].Interval = time.Hour
	writer := mustOpen(t, cfg)
	defer writer.Close()
	if err := writer.Read(t.Context(), func(db *sql.DB) error {
		_, err := db.Exec("PRAGMA auto_vacuum = FULL")
		return err
	}); err != nil {
		t.Fatal(err)
	}
	mustWrite(t, writer, "CREATE TABLE items (id INTEGER PRIMARY KEY, body TEXT NOT NULL)")
	mustWrite(t, writer, "WITH RECURSIVE n(x) AS (SELECT 1 UNION ALL SELECT x + 1 FROM n WHERE x < 2000) INSERT INTO items (body) SELECT hex(randomblob(500)) FROM n")

	readerCfg := testConfig(t, replica)
	readerCfg.CompactionLevels = cfg.CompactionLevels
	reader := mustOpen(t, readerCfg)
	defer reader.Close()
	if n := count(t, reader, "items"); n != 2000 {
		t.Fatalf("reader has %d rows before the delete, want 2000", n)
	}

	mustWrite(t, writer, "DELETE FROM items WHERE id > 100")
	for deadline := time.Now().Add(5 * time.Second); ; time.Sleep(10 * time.Millisecond) {
		n, err := rowCount(t.Context(), reader, "items")
		if err != nil || (n != 2000 && n != 100) {
			t.Fatalf("reader after the delete: %d rows, %v; want 2000 or 100", n, err)
		}
		if n == 100 {
			break
		}
		if time.Now().After(deadline) {
			t.Fatal("reader never saw the delete")
		}
	}
	var check string
	if err := reader.Read(t.Context(), func(db *sql.DB) error {
		return db.QueryRow("PRAGMA integrity_check").Scan(&check)
	}); err != nil || check != "ok" {
		t.Fatalf("reader integrity_check = %q, %v", check, err)
	}
}

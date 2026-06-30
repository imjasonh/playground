package tables_test

import (
	"testing"

	sqlite3 "github.com/ncruces/go-sqlite3"
	sqlite3driver "github.com/ncruces/go-sqlite3/driver"

	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
	"github.com/imjasonh/playground/gitdb/internal/tables"
)

func TestNcrucesBackend(t *testing.T) {
	dir, _, head := buildRepo(t)
	manager, err := gitrepo.NewManager(gitrepo.Options{CacheDir: t.TempDir()})
	if err != nil {
		t.Fatal(err)
	}
	tables.Init(manager)

	db, err := sqlite3driver.Open(":memory:", func(conn *sqlite3.Conn) error {
		return tables.RegisterNcruces(conn)
	})
	if err != nil {
		t.Fatal(err)
	}
	db.SetMaxOpenConns(1)
	db.SetMaxIdleConns(1)
	t.Cleanup(func() { db.Close() })

	if err := tables.CreateAll(db, dir); err != nil {
		t.Fatal(err)
	}

	if got := scalar(t, db, "SELECT count(*) FROM commits"); got != int64(2) {
		t.Errorf("commit count = %v, want 2", got)
	}
	if got := scalar(t, db, "SELECT count(*) FROM commits WHERE hash = ?", head.String()); got != int64(1) {
		t.Errorf("hash pushdown count = %v, want 1", got)
	}
	rows := query(t, db, `
		SELECT c.author_name, sum(cf.additions)
		FROM commit_files AS cf
		JOIN commits AS c ON c.hash = cf.commit_hash
		GROUP BY c.author_name
		ORDER BY c.author_name`)
	if len(rows) != 2 || rows[0][0] != "Alice" || rows[1][0] != "Bob" {
		t.Errorf("join rows = %v, want Alice and Bob", rows)
	}
}

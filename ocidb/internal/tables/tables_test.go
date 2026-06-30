package tables_test

import (
	"database/sql"
	"fmt"
	"reflect"
	"testing"

	_ "modernc.org/sqlite"

	"github.com/imjasonh/playground/ocidb/internal/registry"
	"github.com/imjasonh/playground/ocidb/internal/registrytest"
	"github.com/imjasonh/playground/ocidb/internal/tables"
)

func setup(t *testing.T) (*sql.DB, *registrytest.Fake) {
	t.Helper()
	f := registrytest.New()
	client, err := registry.New(registry.Options{Dir: t.TempDir(), Backend: f})
	if err != nil {
		t.Fatalf("registry.New: %v", err)
	}
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("open sqlite: %v", err)
	}
	db.SetMaxOpenConns(1)
	t.Cleanup(func() { db.Close() })
	if err := tables.Install(db, client); err != nil {
		t.Fatalf("Install: %v", err)
	}
	return db, f
}

func query(t *testing.T, db *sql.DB, q string) [][]any {
	t.Helper()
	rows, err := db.Query(q)
	if err != nil {
		t.Fatalf("query %q: %v", q, err)
	}
	defer rows.Close()
	cols, err := rows.Columns()
	if err != nil {
		t.Fatal(err)
	}
	var out [][]any
	for rows.Next() {
		cells := make([]any, len(cols))
		ptrs := make([]any, len(cols))
		for i := range cells {
			ptrs[i] = &cells[i]
		}
		if err := rows.Scan(ptrs...); err != nil {
			t.Fatal(err)
		}
		out = append(out, cells)
	}
	if err := rows.Err(); err != nil {
		t.Fatalf("query %q: %v", q, err)
	}
	return out
}

func queryErr(db *sql.DB, q string) error {
	rows, err := db.Query(q)
	if err != nil {
		return err
	}
	defer rows.Close()
	cols, _ := rows.Columns()
	for rows.Next() {
		cells := make([]any, len(cols))
		ptrs := make([]any, len(cells))
		for i := range cells {
			ptrs[i] = &cells[i]
		}
		_ = rows.Scan(ptrs...)
	}
	return rows.Err()
}

func TestTags(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT tag FROM tags WHERE repository = 'demo' ORDER BY tag`)
	want := [][]any{{"1.0"}, {"2.0"}, {"2.1"}, {"latest"}}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("tags = %v, want %v", got, want)
	}
}

func TestRequiredParamError(t *testing.T) {
	db, _ := setup(t)
	for _, q := range []string{
		`SELECT tag FROM tags`,
		`SELECT digest FROM manifest`,
		`SELECT * FROM layers`,
	} {
		if err := queryErr(db, q); err == nil {
			t.Errorf("%q: expected an error about a required parameter", q)
		}
	}
}

func TestSelectStarHidesHiddenColumns(t *testing.T) {
	db, _ := setup(t)

	// Close each result set before issuing the next query: the DB is pinned to
	// a single connection, so overlapping open rows would deadlock.
	if want := []string{"tag"}; !reflect.DeepEqual(columnsOf(t, db, `SELECT * FROM tags WHERE repository = 'demo'`), want) {
		t.Fatalf("tags SELECT * columns should be %v (repository is HIDDEN)", want)
	}
	icols := columnsOf(t, db, `SELECT * FROM image WHERE reference = 'demo'`)
	if len(icols) == 0 || icols[0] != "digest" {
		t.Fatalf("image SELECT * first column = %v, want digest (reference/platform are HIDDEN)", icols)
	}
}

// columnsOf returns the result columns of a query and closes the rows promptly.
func columnsOf(t *testing.T, db *sql.DB, q string) []string {
	t.Helper()
	rows, err := db.Query(q)
	if err != nil {
		t.Fatal(err)
	}
	defer rows.Close()
	cols, err := rows.Columns()
	if err != nil {
		t.Fatal(err)
	}
	return cols
}

func TestManifestIndexAndSingle(t *testing.T) {
	db, _ := setup(t)

	idx := query(t, db, `SELECT is_index, num_manifests, num_layers FROM manifest WHERE reference = 'demo'`)
	if len(idx) != 1 {
		t.Fatalf("rows = %d, want 1", len(idx))
	}
	if got := idx[0][0].(int64); got != 1 {
		t.Errorf("is_index = %d, want 1", got)
	}
	if got := idx[0][1].(int64); got != 3 {
		t.Errorf("num_manifests = %d, want 3", got)
	}
	if idx[0][2] != nil {
		t.Errorf("num_layers = %v, want NULL for an index", idx[0][2])
	}

	single := query(t, db, `SELECT is_index, num_layers, config_digest FROM manifest WHERE reference = 'single'`)
	if got := single[0][0].(int64); got != 0 {
		t.Errorf("single is_index = %d, want 0", got)
	}
	if got := single[0][1].(int64); got != 1 {
		t.Errorf("single num_layers = %d, want 1", got)
	}
	if single[0][2] == nil {
		t.Error("single config_digest should not be NULL")
	}
}

func TestPlatforms(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT os, architecture, variant FROM platforms WHERE reference = 'demo' ORDER BY architecture`)
	want := [][]any{
		{"linux", "amd64", nil},
		{"linux", "arm64", "v8"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("platforms = %v, want %v (attestation excluded)", got, want)
	}
}

func TestLayersDefaultAndExplicitPlatform(t *testing.T) {
	db, _ := setup(t)

	def := query(t, db, `SELECT size FROM layers WHERE reference = 'demo' ORDER BY ordinal`)
	if want := [][]any{{int64(1000)}, {int64(2000)}}; !reflect.DeepEqual(def, want) {
		t.Fatalf("default-platform layer sizes = %v, want %v", def, want)
	}

	arm := query(t, db, `SELECT size FROM layers WHERE reference = 'demo' AND platform = 'linux/arm64' ORDER BY ordinal`)
	if want := [][]any{{int64(1100)}, {int64(2100)}}; !reflect.DeepEqual(arm, want) {
		t.Fatalf("arm64 layer sizes = %v, want %v", arm, want)
	}
}

func TestImage(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT architecture, num_layers, total_size, num_env, num_labels, num_exposed_ports, user, working_dir, entrypoint, cmd FROM image WHERE reference = 'demo'`)
	if len(got) != 1 {
		t.Fatalf("rows = %d, want 1", len(got))
	}
	row := got[0]
	checks := []struct {
		name string
		got  any
		want any
	}{
		{"architecture", row[0], "amd64"},
		{"num_layers", row[1], int64(2)},
		{"total_size", row[2], int64(3000)},
		{"num_env", row[3], int64(2)},
		{"num_labels", row[4], int64(2)},
		{"num_exposed_ports", row[5], int64(1)},
		{"user", row[6], "1000"},
		{"working_dir", row[7], "/app"},
		{"entrypoint", row[8], `["/entrypoint.sh"]`},
		{"cmd", row[9], `["sh"]`},
	}
	for _, c := range checks {
		if !reflect.DeepEqual(c.got, c.want) {
			t.Errorf("%s = %v (%T), want %v", c.name, c.got, c.got, c.want)
		}
	}
}

func TestHistory(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT ordinal, created_by, empty_layer FROM history WHERE reference = 'demo' ORDER BY ordinal`)
	if len(got) != 3 {
		t.Fatalf("history rows = %d, want 3", len(got))
	}
	if got[0][1] != "ADD rootfs / # buildkit" {
		t.Errorf("first step = %v", got[0][1])
	}
	if got[2][2].(int64) != 1 {
		t.Errorf("last step empty_layer = %v, want 1", got[2][2])
	}
}

func TestEnvAndLabels(t *testing.T) {
	db, _ := setup(t)

	env := query(t, db, `SELECT key, value FROM env WHERE reference = 'demo' ORDER BY key`)
	wantEnv := [][]any{{"DEMO", "1"}, {"PATH", "/usr/local/bin:/usr/bin"}}
	if !reflect.DeepEqual(env, wantEnv) {
		t.Fatalf("env = %v, want %v", env, wantEnv)
	}

	labels := query(t, db, `SELECT key, value FROM labels WHERE reference = 'demo' ORDER BY key`)
	wantLabels := [][]any{{"maintainer", "ocidb"}, {"org.opencontainers.image.title", "demo"}}
	if !reflect.DeepEqual(labels, wantLabels) {
		t.Fatalf("labels = %v, want %v", labels, wantLabels)
	}
}

// TestJoinPushesDownBothParams is the regression test for the BestIndex cost
// model: a join must bind BOTH the constant reference and the per-row platform,
// rather than falling back to the default platform for every row.
func TestJoinPushesDownBothParams(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `
		WITH p(platform) AS (VALUES ('linux/amd64'), ('linux/arm64'))
		SELECT p.platform, count(*) AS layers, sum(l.size) AS total
		FROM p JOIN layers l ON l.reference = 'demo' AND l.platform = p.platform
		GROUP BY p.platform ORDER BY p.platform`)
	want := [][]any{
		{"linux/amd64", int64(2), int64(3000)},
		{"linux/arm64", int64(2), int64(3200)},
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("join result = %v, want %v (platform must be pushed down per row)", got, want)
	}
}

func TestQueriesAreCached(t *testing.T) {
	db, f := setup(t)
	for i := 0; i < 4; i++ {
		query(t, db, `SELECT architecture FROM image WHERE reference = 'demo'`)
	}
	manifests, blobs, _ := f.Calls()
	// Resolving demo (an index) once needs: index manifest + amd64 child
	// manifest (2) and the amd64 config blob (1). Repeats must be cache hits.
	if manifests != 2 || blobs != 1 {
		t.Fatalf("network calls = %d manifests + %d blobs, want 2 + 1 (rest cached)", manifests, blobs)
	}
}

func TestSchemaAndNames(t *testing.T) {
	names := tables.Names()
	if len(names) != 8 {
		t.Fatalf("table count = %d, want 8", len(names))
	}
	for _, n := range names {
		if tables.Schema(n) == "" {
			t.Errorf("missing schema for %q", n)
		}
	}
	if tables.Schema("does-not-exist") != "" {
		t.Error("expected empty schema for unknown table")
	}
	_ = fmt.Sprint(names) // keep fmt import if checks change
}

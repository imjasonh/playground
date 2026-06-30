package tables_test

import (
	"database/sql"
	"fmt"
	"reflect"
	"strings"
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

func TestFilesListing(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT layer, path, type, linkname, mode FROM files WHERE reference = 'demo' ORDER BY layer, path`)
	if len(got) != 8 {
		t.Fatalf("file count = %d, want 8: %v", len(got), got)
	}
	byPath := map[string][]any{}
	for _, r := range got {
		byPath[r[1].(string)] = r
	}
	type want struct {
		layer    int64
		typ      string
		linkname any
		mode     string
	}
	checks := map[string]want{
		"/etc/":            {1, "dir", nil, "0755"},
		"/etc/os-release":  {1, "file", nil, "0644"},
		"/usr/bin/su":      {1, "file", nil, "4755"},
		"/bin/sh":          {1, "symlink", "busybox", "0777"},
		"/app/run.sh":      {2, "file", nil, "0755"},
		"/app/config.json": {2, "file", nil, "0644"},
	}
	for p, w := range checks {
		r, ok := byPath[p]
		if !ok {
			t.Errorf("missing file %q", p)
			continue
		}
		if r[0].(int64) != w.layer {
			t.Errorf("%s layer = %v, want %d", p, r[0], w.layer)
		}
		if r[2] != w.typ {
			t.Errorf("%s type = %v, want %q", p, r[2], w.typ)
		}
		if !reflect.DeepEqual(r[3], w.linkname) {
			t.Errorf("%s linkname = %v, want %v", p, r[3], w.linkname)
		}
		if r[4] != w.mode {
			t.Errorf("%s mode = %v, want %q", p, r[4], w.mode)
		}
	}
}

func TestFilesContentByPath(t *testing.T) {
	db, _ := setup(t)
	// Path equality is pushed down, so exactly one row comes back.
	got := query(t, db, `SELECT content FROM files WHERE reference = 'demo' AND path = '/etc/os-release'`)
	if len(got) != 1 {
		t.Fatalf("rows = %d, want 1", len(got))
	}
	if got[0][0] == nil || !strings.Contains(got[0][0].(string), `Demo Linux (amd64)`) {
		t.Fatalf("content = %v, want os-release text", got[0][0])
	}
}

func TestFilesBinaryContentIsNull(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT size, content, mode FROM files WHERE reference = 'demo' AND path = '/usr/bin/su'`)
	if len(got) != 1 {
		t.Fatalf("rows = %d, want 1", len(got))
	}
	if got[0][0].(int64) != 8 {
		t.Errorf("size = %v, want 8", got[0][0])
	}
	if got[0][1] != nil {
		t.Errorf("content = %v, want NULL for a binary file", got[0][1])
	}
	if got[0][2] != "4755" {
		t.Errorf("mode = %v, want 4755 (setuid)", got[0][2])
	}
}

func TestFilesPlatformContent(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT content FROM files WHERE reference = 'demo' AND platform = 'linux/arm64' AND path = '/etc/os-release'`)
	if len(got) != 1 || got[0][0] == nil || !strings.Contains(got[0][0].(string), `Demo Linux (arm64)`) {
		t.Fatalf("arm64 os-release content = %v, want arm64 text", got)
	}
}

// TestFilesContentServedFromCache exercises the content gating + caching: after
// a metadata-only listing has warmed the per-layer TOC and blob caches, reading
// a file's content must not trigger any new registry blob fetches.
func TestFilesContentServedFromCache(t *testing.T) {
	db, f := setup(t)
	query(t, db, `SELECT path FROM files WHERE reference = 'demo' ORDER BY path`)
	_, blobsBefore, _ := f.Calls()

	got := query(t, db, `SELECT content FROM files WHERE reference = 'demo' AND path = '/app/run.sh'`)
	_, blobsAfter, _ := f.Calls()

	if blobsAfter != blobsBefore {
		t.Fatalf("content read caused %d new blob fetches, want 0 (cached)", blobsAfter-blobsBefore)
	}
	if len(got) != 1 || got[0][0] == nil || !strings.Contains(got[0][0].(string), "hello from amd64") {
		t.Fatalf("run.sh content = %v", got)
	}
}

func TestFilesSquashedView(t *testing.T) {
	db, _ := setup(t)
	// present = 1 is the final, squashed filesystem: replaced/deleted entries
	// and whiteout markers are gone.
	got := query(t, db, `SELECT path FROM files WHERE reference = 'overlay' AND present = 1 ORDER BY path`)
	var paths []string
	for _, r := range got {
		paths = append(paths, r[0].(string))
	}
	want := []string{
		"/data/",
		"/etc/",
		"/etc/added.txt",
		"/etc/keep.txt",
		"/etc/replaced.txt",
		"/opaquedir/",
		"/opaquedir/new.txt",
	}
	if !reflect.DeepEqual(paths, want) {
		t.Fatalf("squashed paths = %v, want %v", paths, want)
	}
}

func TestFilesReplacedAndDeleted(t *testing.T) {
	db, _ := setup(t)
	// Real file bytes that don't survive to the final FS: replaced by a higher
	// layer or removed by a whiteout. Exclude the (tiny) whiteout markers.
	got := query(t, db, `
		SELECT path, layer, size FROM files
		WHERE reference = 'overlay' AND present = 0 AND type = 'file' AND whiteout IS NULL
		ORDER BY path`)
	want := [][]any{
		{"/data/old.bin", int64(1), int64(len("old binary data"))},
		{"/etc/replaced.txt", int64(1), int64(len("version 1\n"))},
		{"/opaquedir/lower.txt", int64(1), int64(len("lower\n"))},
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("replaced/deleted files = %v, want %v", got, want)
	}
}

func TestFilesWhiteoutMarkers(t *testing.T) {
	db, _ := setup(t)
	got := query(t, db, `SELECT path, whiteout FROM files WHERE reference = 'overlay' AND whiteout IS NOT NULL ORDER BY path`)
	want := [][]any{
		{"/data/.wh.old.bin", "file"},
		{"/opaquedir/.wh..wh..opq", "opaque"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("whiteout markers = %v, want %v", got, want)
	}
}

func TestFilesSquashedContentWinsFromHigherLayer(t *testing.T) {
	db, _ := setup(t)
	// Layered view: /etc/replaced.txt appears in two layers.
	layered := query(t, db, `SELECT layer, present FROM files WHERE reference = 'overlay' AND path = '/etc/replaced.txt' ORDER BY layer`)
	want := [][]any{{int64(1), int64(0)}, {int64(2), int64(1)}}
	if !reflect.DeepEqual(layered, want) {
		t.Fatalf("layered replaced.txt = %v, want %v", layered, want)
	}
	// Squashed view: only the higher layer's content is current.
	squashed := query(t, db, `SELECT content FROM files WHERE reference = 'overlay' AND path = '/etc/replaced.txt' AND present = 1`)
	if len(squashed) != 1 || squashed[0][0] != "version 2 is longer\n" {
		t.Fatalf("squashed replaced.txt content = %v, want the layer-2 version", squashed)
	}
}

func TestSchemaAndNames(t *testing.T) {
	names := tables.Names()
	if len(names) != 9 {
		t.Fatalf("table count = %d, want 9", len(names))
	}
	want := map[string]bool{}
	for _, n := range names {
		want[n] = true
		if tables.Schema(n) == "" {
			t.Errorf("missing schema for %q", n)
		}
	}
	if !want["files"] {
		t.Errorf("expected a 'files' table in %v", names)
	}
	if tables.Schema("does-not-exist") != "" {
		t.Error("expected empty schema for unknown table")
	}
	_ = fmt.Sprint(names) // keep fmt import if checks change
}

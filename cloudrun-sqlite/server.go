package main

import (
	"context"
	"database/sql"
	"encoding/json"
	"errors"
	"html/template"
	"io"
	"net/http"
	"strconv"
	"time"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/litevfs"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

func migrate(ctx context.Context, st *store.Store) error {
	return st.Write(ctx, func(tx *sql.Tx) error {
		_, err := tx.ExecContext(ctx, `
			CREATE TABLE IF NOT EXISTS counters (name TEXT PRIMARY KEY, n INTEGER NOT NULL);
			CREATE TABLE IF NOT EXISTS items (id INTEGER PRIMARY KEY, body TEXT NOT NULL);
		`)
		return err
	})
}

type server struct {
	st       *store.Store
	instance string
	started  time.Time
}

func newServer(st *store.Store, instance string, started time.Time) *server {
	return &server{st: st, instance: instance, started: started}
}

func (s *server) routes() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /{$}", s.index)
	mux.HandleFunc("POST /click", s.click)
	mux.HandleFunc("GET /items/{id}", s.getItem)
	mux.HandleFunc("POST /items", s.createItem)
	mux.HandleFunc("GET /stats", s.stats)
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "ok\n") })
	mux.HandleFunc("POST /admin/snapshot", s.snapshot)
	mux.HandleFunc("GET /admin/check", s.check)
	return mux
}

// writeError maps store errors to HTTP statuses. A conflict that survived
// every retry means another instance kept winning; the client can retry.
func writeError(w http.ResponseWriter, err error) {
	code := http.StatusInternalServerError
	switch {
	case errors.Is(err, litevfs.ErrConflict), errors.Is(err, store.ErrClosed):
		w.Header().Set("Retry-After", "1")
		code = http.StatusServiceUnavailable
	case errors.Is(err, sql.ErrNoRows):
		code = http.StatusNotFound
	case errors.Is(err, context.Canceled), errors.Is(err, context.DeadlineExceeded):
		code = http.StatusGatewayTimeout
	}
	http.Error(w, err.Error(), code)
}

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(v)
}

func (s *server) clicks(ctx context.Context) (int64, error) {
	var n int64
	err := s.st.Read(ctx, func(db *sql.DB) error {
		err := db.QueryRowContext(ctx, "SELECT n FROM counters WHERE name = 'clicks'").Scan(&n)
		if errors.Is(err, sql.ErrNoRows) {
			return nil
		}
		return err
	})
	return n, err
}

func (s *server) index(w http.ResponseWriter, r *http.Request) {
	n, err := s.clicks(r.Context())
	if err != nil {
		writeError(w, err)
		return
	}
	var version string
	s.st.Read(r.Context(), func(db *sql.DB) error {
		return db.QueryRowContext(r.Context(), "SELECT sqlite_version()").Scan(&version)
	})
	page.Execute(w, map[string]any{"Count": n, "Version": version, "Instance": s.instance})
}

func (s *server) click(w http.ResponseWriter, r *http.Request) {
	var n int64
	if err := s.st.Write(r.Context(), func(tx *sql.Tx) error {
		return tx.QueryRowContext(r.Context(), `
			INSERT INTO counters (name, n) VALUES ('clicks', 1)
			ON CONFLICT (name) DO UPDATE SET n = n + 1
			RETURNING n`).Scan(&n)
	}); err != nil {
		writeError(w, err)
		return
	}
	counter.Execute(w, map[string]any{"Count": n})
}

func (s *server) getItem(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.ParseInt(r.PathValue("id"), 10, 64)
	if err != nil {
		http.Error(w, "bad id", http.StatusBadRequest)
		return
	}
	var body string
	if err := s.st.Read(r.Context(), func(db *sql.DB) error {
		return db.QueryRowContext(r.Context(), "SELECT body FROM items WHERE id = ?", id).Scan(&body)
	}); err != nil {
		writeError(w, err)
		return
	}
	writeJSON(w, map[string]any{"id": id, "body": body})
}

func (s *server) createItem(w http.ResponseWriter, r *http.Request) {
	body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, 1<<20))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	var id int64
	if err := s.st.Write(r.Context(), func(tx *sql.Tx) error {
		return tx.QueryRowContext(r.Context(), "INSERT INTO items (body) VALUES (?) RETURNING id", string(body)).Scan(&id)
	}); err != nil {
		writeError(w, err)
		return
	}
	w.WriteHeader(http.StatusCreated)
	writeJSON(w, map[string]any{"id": id})
}

func (s *server) stats(w http.ResponseWriter, r *http.Request) {
	writeJSON(w, map[string]any{
		"instance":  s.instance,
		"uptime_ms": ms(time.Since(s.started)),
		"store":     s.st.Stats(r.Context()),
	})
}

func (s *server) snapshot(w http.ResponseWriter, r *http.Request) {
	res, err := s.st.Snapshot(r.Context())
	if err != nil {
		writeError(w, err)
		return
	}
	writeJSON(w, res)
}

// check runs PRAGMA integrity_check, which reads every page.
func (s *server) check(w http.ResponseWriter, r *http.Request) {
	var integrity string
	var items, maxID int64
	if err := s.st.Read(r.Context(), func(db *sql.DB) error {
		if err := db.QueryRowContext(r.Context(), "PRAGMA integrity_check").Scan(&integrity); err != nil {
			return err
		}
		return db.QueryRowContext(r.Context(), "SELECT count(*), coalesce(max(id), 0) FROM items").Scan(&items, &maxID)
	}); err != nil {
		writeError(w, err)
		return
	}
	writeJSON(w, map[string]any{"integrity": integrity, "items": items, "max_id": maxID})
}

var (
	page = template.Must(template.New("page").Parse(`<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>cloudrun-sqlite</title>
<script src="https://unpkg.com/htmx.org@2.0.0" integrity="sha384-wS5l5IKJBvK6sPTKa2WZ1js3d947pvWXbPJ1OmWfEuxLgeHcEbjUUA5i9V5ZkpCw" crossorigin="anonymous"></script>
<style>
body { font-family: system-ui, sans-serif; max-width: 32rem; margin: 3rem auto; padding: 0 1rem; line-height: 1.5; }
@keyframes highlight { from { background: #fff3a0; } to { background: none; } }
.highlight { animation: highlight 1s; }
button { font: inherit; padding: 0.5rem 1rem; }
small { color: #555; }
</style>
</head>
<body>
<h1>cloudrun-sqlite</h1>
<p><small>SQLite {{.Version}} on a Litestream replica. Instance {{.Instance}}.</small></p>
{{template "counter" .}}
</body>
</html>
{{define "counter"}}<div id="counter" hx-swap="outerHTML">
<p class="highlight">Clicks: {{.Count}}</p>
<button hx-post="/click" hx-target="#counter">Click</button>
</div>{{end}}`))

	counter = page.Lookup("counter")
)

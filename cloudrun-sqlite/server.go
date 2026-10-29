package main

import (
	"context"
	"crypto/subtle"
	"database/sql"
	"embed"
	"encoding/json"
	"errors"
	"fmt"
	"html/template"
	"io"
	"log/slog"
	"net/http"
	"strconv"
	"strings"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/fanout"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

//go:embed web/vendor/htmx.js web/vendor/sse.js
var webFiles embed.FS

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
	st         *store.Store
	live       *fanout.Hub
	instance   string
	started    time.Time
	adminToken string
	// readOnly serves a replica that never writes. writerURL, when set,
	// is where its page links for clicking.
	readOnly  bool
	writerURL string
	// pollInterval is how often the replica's VFS lists for new writes.
	pollInterval time.Duration
}

func newServer(st *store.Store, live *fanout.Hub, instance string, started time.Time, adminToken string) *server {
	return &server{st: st, live: live, instance: instance, started: started, adminToken: adminToken}
}

func (s *server) routes() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /{$}", s.index)
	mux.HandleFunc("GET /events", s.events)
	mux.HandleFunc("GET /htmx.js", script("web/vendor/htmx.js"))
	mux.HandleFunc("GET /sse.js", script("web/vendor/sse.js"))
	mux.HandleFunc("GET /items/{id}", s.getItem)
	mux.HandleFunc("GET /stats", s.stats)
	mux.Handle("GET /metrics", observe.Metrics())
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "ok\n") })
	mux.HandleFunc("GET /admin/check", s.admin(s.check))
	if s.readOnly {
		for _, pattern := range []string{"POST /click", "POST /items", "POST /admin/snapshot"} {
			mux.HandleFunc(pattern, s.refuseWrite)
		}
	} else {
		mux.HandleFunc("POST /click", s.click)
		mux.HandleFunc("POST /items", s.createItem)
		mux.HandleFunc("POST /admin/snapshot", s.admin(s.snapshot))
	}
	return observe.HTTP(mux)
}

// refuseWrite answers a write sent to a read-only replica. The empty Allow
// header says that the resource accepts no methods here.
func (s *server) refuseWrite(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Allow", "")
	msg := "read-only replica: send writes to the writer"
	if s.writerURL != "" {
		msg += " at " + s.writerURL
	}
	http.Error(w, msg, http.StatusMethodNotAllowed)
}

// followReplica sends the click count to connected pages when it changes.
// A read-only replica handles no clicks, so the count changes only when the
// VFS installs another instance's writes, on its poll. Checking more often
// than every second would only reread cached pages.
func (s *server) followReplica(ctx context.Context) {
	every := min(s.pollInterval, time.Second)
	if every <= 0 {
		every = time.Second
	}
	t := time.NewTicker(every)
	defer t.Stop()
	last, err := s.clicks(ctx)
	if err != nil {
		slog.Warn("read click count", "error", err)
	}
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		n, err := s.clicks(ctx)
		if err != nil {
			if ctx.Err() == nil {
				slog.Warn("read click count", "error", err)
			}
			continue
		}
		if n > last {
			last = n
			s.live.NotifyClick(n)
		}
	}
}

func script(name string) http.HandlerFunc {
	body, err := webFiles.ReadFile(name)
	if err != nil {
		panic(err)
	}
	return func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/javascript; charset=utf-8")
		w.Header().Set("Cache-Control", "public, max-age=86400")
		w.Write(body)
	}
}

// admin guards endpoints that read the whole database. They are off unless
// ADMIN_TOKEN is set, and then require it as a bearer token.
func (s *server) admin(h http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if s.adminToken == "" {
			http.NotFound(w, r)
			return
		}
		got := strings.TrimPrefix(r.Header.Get("Authorization"), "Bearer ")
		if subtle.ConstantTimeCompare([]byte(got), []byte(s.adminToken)) != 1 {
			http.Error(w, "unauthorized", http.StatusUnauthorized)
			return
		}
		h(w, r)
	}
}

// writeError maps store errors to HTTP statuses. A conflict that survived
// every retry means another instance kept winning, and an unavailable
// database is waiting to be reopened; the client can retry either.
func writeError(w http.ResponseWriter, err error) {
	code := http.StatusInternalServerError
	switch {
	case errors.Is(err, litestream.ErrConflict), errors.Is(err, store.ErrClosed), errors.Is(err, store.ErrUnavailable):
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
	v := view{Count: n, Version: version, Instance: s.instance, ReadOnly: s.readOnly, WriterURL: s.writerURL}
	if s.readOnly {
		v.Poll = s.pollInterval.String()
	}
	if err := page.Execute(w, v); err != nil {
		slog.Error("render index", "error", err)
	}
}

type view struct {
	Count     int64
	Version   string
	Instance  string
	Took      string
	ReadOnly  bool
	WriterURL string
	Poll      string
}

func (s *server) click(w http.ResponseWriter, r *http.Request) {
	var n int64
	start := time.Now()
	if err := s.st.Write(r.Context(), func(tx *sql.Tx) error {
		return tx.QueryRowContext(r.Context(), `
			INSERT INTO counters (name, n) VALUES ('clicks', 1)
			ON CONFLICT (name) DO UPDATE SET n = n + 1
			RETURNING n`).Scan(&n)
	}); err != nil {
		writeError(w, err)
		return
	}
	// The replica has the count before this call, so a page that misses
	// the in-memory delivery (a crash, a dropped connection) still reads
	// the correct count on its next connection.
	s.live.NotifyClick(n)
	if err := actions.Execute(w, view{Took: writeTook(time.Since(start))}); err != nil {
		slog.Error("render click", "error", err)
	}
}

// events sends the current count, then each later click, as a server-sent
// event. The count on the wire only moves forward: concurrent requests can
// notify out of order after they share one transaction.
func (s *server) events(w http.ResponseWriter, r *http.Request) {
	clicks, unsub := s.live.Subscribe()
	defer unsub()
	n, err := s.clicks(r.Context())
	if err != nil {
		writeError(w, err)
		return
	}
	w.Header().Set("Content-Type", "text/event-stream")
	w.Header().Set("Cache-Control", "no-cache")
	rc := http.NewResponseController(w)
	if err := writeEvent(w, "clicks", countHTML(n, false)); err != nil {
		return
	}
	if err := rc.Flush(); err != nil {
		return
	}
	ping := time.NewTicker(15 * time.Second)
	defer ping.Stop()
	last := n
	for {
		select {
		case <-r.Context().Done():
			return
		case <-ping.C:
			if _, err := io.WriteString(w, ": ping\n\n"); err != nil {
				return
			}
			if err := rc.Flush(); err != nil {
				return
			}
		case c, ok := <-clicks:
			if !ok || c.Count <= last {
				if !ok {
					return
				}
				continue
			}
			last = c.Count
			if err := writeEvent(w, "clicks", countHTML(c.Count, true)); err != nil {
				return
			}
			if err := writeEvent(w, "notice", fmt.Sprintf("<li>Notification %d, count %d.</li>", c.ID, c.Count)); err != nil {
				return
			}
			if err := rc.Flush(); err != nil {
				return
			}
		}
	}
}

func countHTML(n int64, highlight bool) string {
	if highlight {
		return fmt.Sprintf(`<span class="highlight">Clicks: %d</span>`, n)
	}
	return fmt.Sprintf("Clicks: %d", n)
}

func writeEvent(w io.Writer, name, data string) error {
	_, err := fmt.Fprintf(w, "event: %s\ndata: %s\n\n", name, data)
	return err
}

// writeTook reports a durable write's duration for the click button.
func writeTook(d time.Duration) string {
	d = d.Round(time.Millisecond)
	switch {
	case d < time.Millisecond:
		return "under 1 ms"
	case d < time.Second:
		return strconv.FormatInt(d.Milliseconds(), 10) + " ms"
	default:
		return strconv.FormatFloat(d.Seconds(), 'f', 1, 64) + " s"
	}
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
<script src="/htmx.js"></script>
<script src="/sse.js"></script>
<style>
body { font-family: system-ui, sans-serif; font-size: 1.125rem; line-height: 1.6; max-width: 65ch; margin: 3rem auto; padding: 0 1rem; color: #1a1a1a; background: #fff; }
h1 { font-size: 2rem; line-height: 1.2; font-weight: 650; margin: 0 0 0.5em; text-wrap: balance; }
h2 { font-size: 1.35rem; line-height: 1.25; font-weight: 600; margin: 1.5em 0 0.5em; text-wrap: balance; }
p { margin: 0.8em 0; }
a { color: #0b3a82; }
a:visited { color: #4c1d95; }
code { font-family: ui-monospace, monospace; font-size: 0.9em; }
@keyframes highlight { from { background: #fff3a0; } to { background: transparent; } }
.highlight { animation: highlight 1s; }
button { font: inherit; padding: 0.6rem 1rem; }
button:disabled { opacity: 0.55; }
button:focus-visible { outline: 3px solid #0b3a82; outline-offset: 2px; }
.actions { display: flex; align-items: baseline; gap: 0.75rem; flex-wrap: wrap; }
#count { font-weight: 600; }
#log { margin: 0.5em 0 0; padding-left: 1.25rem; }
#log li { margin: 0.25rem 0; }
.status { color: #333; }
@media (prefers-reduced-motion: reduce) {
  .highlight { animation: none; }
}
</style>
</head>
<body hx-ext="sse">
<h1>cloudrun-sqlite{{if .ReadOnly}} read-only replica{{end}}</h1>
{{if .ReadOnly}}<p>The click count is one row in SQLite. This instance reads the database through <a href="https://litestream.io">Litestream</a> and never writes: SQLite opens it read-only, and this service's account can only read the bucket.</p>
<p>Each open page holds a server-sent event connection to this instance. Litestream lists the replica for new writes every {{.Poll}}. When the count changes, this instance sends it to every page connected here.</p>
<p>A click reaches this page one poll after the writer uploads it.{{if .WriterURL}} <a href="{{.WriterURL}}">Click on the writer</a>.{{end}}</p>
{{else}}<p>The click count is one row in SQLite. This process is the writer. <a href="https://litestream.io">Litestream</a> uploads the transaction to the replica before it answers the click.</p>
<p>Each open page holds a server-sent event connection to this process. After the upload, the same request delivers the new count, in memory, to every page connected here.</p>
<p>That delivery stays in this process. A read-only replica reads the new count from the replica on its next poll. A page connected to the writer gets the count straight from the request that produced it.</p>
{{end}}<p class="status">SQLite {{.Version}}. Instance {{.Instance}}.</p>
<div sse-connect="/events">
<p id="count" sse-swap="clicks" hx-swap="innerHTML" aria-live="polite">Clicks: {{.Count}}</p>
{{if not .ReadOnly}}{{template "actions" .}}{{end}}
<h2>Notifications this page received</h2>
<ol id="log" sse-swap="notice" hx-swap="beforeend" aria-live="polite"></ol>
</div>
</body>
</html>
{{define "actions"}}<div class="actions" id="actions">
<button hx-post="/click" hx-target="#actions" hx-swap="outerHTML" hx-disabled-elt="this">Click</button>
{{if .Took}}<span class="status">{{.Took}}</span>{{end}}
</div>{{end}}`))

	actions = page.Lookup("actions")
)

func init() {
	if actions == nil {
		panic("missing actions template")
	}
}

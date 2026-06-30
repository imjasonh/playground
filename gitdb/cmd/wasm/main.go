//go:build js && wasm

// Command wasm runs the gitdb browser spike in a Web Worker.
package main

import (
	"context"
	"database/sql"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"strings"
	"syscall/js"
	"time"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/storage/memory"
	sqlite3 "github.com/ncruces/go-sqlite3"
	sqlite3driver "github.com/ncruces/go-sqlite3/driver"
	fdw "github.com/values-conflict/go-sqlite-fdw"
	ncrucesfdw "github.com/values-conflict/go-sqlite-fdw/ncruces"

	"github.com/imjasonh/playground/gitdb/internal/browsergit"
	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
	"github.com/imjasonh/playground/gitdb/internal/tables"
	"github.com/imjasonh/playground/gitdb/internal/webquery"
)

const (
	browserSpec   = "browser"
	maxResultRows = 500
	queryTimeout  = 60 * time.Second
	cloneTimeout  = 3 * time.Minute
)

type request struct {
	Type         string `json:"type"`
	ID           string `json:"id"`
	SQL          string `json:"sql"`
	URL          string `json:"url"`
	Proxy        string `json:"proxy"`
	Depth        int    `json:"depth"`
	SingleBranch bool   `json:"singleBranch"`
}

type response struct {
	Type       string           `json:"type"`
	ID         string           `json:"id,omitempty"`
	Error      string           `json:"error,omitempty"`
	Message    string           `json:"message,omitempty"`
	Result     *webquery.Result `json:"result,omitempty"`
	Repository *repositoryInfo  `json:"repository,omitempty"`
}

type repositoryInfo struct {
	URL  string `json:"url"`
	Head string `json:"head,omitempty"`
}

type workerState struct {
	db *sql.DB
}

func main() {
	inbox := make(chan string, 16)
	onMessage := js.FuncOf(func(_ js.Value, args []js.Value) any {
		if len(args) == 0 {
			return nil
		}
		data := args[0].Get("data")
		if data.Type() != js.TypeString {
			post(response{Type: "error", Error: "worker request must be a JSON string"})
			return nil
		}
		select {
		case inbox <- data.String():
		default:
			post(response{Type: "error", Error: "request queue is full"})
		}
		return nil
	})
	defer onMessage.Release()
	js.Global().Call("addEventListener", "message", onMessage)

	post(response{Type: "ready"})
	state := &workerState{}
	defer state.close()
	for raw := range inbox {
		state.handleRequest(raw)
	}
}

func openRepository(repo *git.Repository) (*sql.DB, error) {
	manager, err := gitrepo.NewManager(gitrepo.Options{CacheDir: "memory"})
	if err != nil {
		return nil, err
	}
	if err := manager.Bind(browserSpec, repo); err != nil {
		return nil, err
	}
	tables.Init(manager)

	db, err := sqlite3driver.Open(":memory:", func(conn *sqlite3.Conn) error {
		if err := tables.RegisterNcruces(conn); err != nil {
			return err
		}
		return ncrucesfdw.Register(conn, "browser_http", browserHTTPFactory, browserHTTPFactory)
	})
	if err != nil {
		return nil, err
	}
	db.SetMaxOpenConns(1)
	db.SetMaxIdleConns(1)
	if err := db.Ping(); err != nil {
		db.Close()
		return nil, err
	}
	if err := tables.CreateAll(db, browserSpec); err != nil {
		db.Close()
		return nil, err
	}
	if _, err := db.Exec("CREATE VIRTUAL TABLE network_probe USING browser_http()"); err != nil {
		db.Close()
		return nil, err
	}
	if _, err := db.Exec("PRAGMA query_only = ON"); err != nil {
		db.Close()
		return nil, err
	}
	return db, nil
}

func cloneRepository(ctx context.Context, req request) (*git.Repository, string, error) {
	repoURL, err := browsergit.NormalizeRepositoryURL(req.URL)
	if err != nil {
		return nil, "", err
	}
	cloneURL, err := browsergit.ProxyRepositoryURL(repoURL, req.Proxy)
	if err != nil {
		return nil, "", err
	}
	if req.Depth < 0 || req.Depth > 10_000 {
		return nil, "", errors.New("clone depth must be between 0 and 10000")
	}

	post(response{Type: "progress", ID: req.ID, Message: "Connecting to the Git remote…"})
	repo, err := git.CloneContext(ctx, memory.NewStorage(), nil, &git.CloneOptions{
		URL:               cloneURL,
		NoCheckout:        true,
		Depth:             req.Depth,
		SingleBranch:      req.SingleBranch,
		Tags:              git.AllTags,
		Progress:          progressWriter{id: req.ID},
		RecurseSubmodules: git.NoRecurseSubmodules,
	})
	if err != nil {
		return nil, "", fmt.Errorf("clone %s: %w", repoURL, err)
	}
	return repo, repoURL, nil
}

type progressWriter struct {
	id string
}

func (w progressWriter) Write(data []byte) (int, error) {
	message := strings.TrimSpace(strings.ReplaceAll(string(data), "\r", "\n"))
	if message != "" {
		if len(message) > 240 {
			message = message[len(message)-240:]
		}
		post(response{Type: "progress", ID: w.id, Message: message})
	}
	return len(data), nil
}

// browserHTTPFactory is a deliberately small network-backed FDW used to prove
// that a Go browser fetch can suspend and resume from inside Cursor.Filter.
func browserHTTPFactory(fdw.ConnectArgs) (fdw.Source, string, error) {
	return &browserHTTPSource{},
		"CREATE TABLE x(http_status INTEGER, body TEXT, url TEXT HIDDEN)",
		nil
}

type browserHTTPSource struct{}

func (*browserHTTPSource) BestIndex(info *fdw.IndexInfo) error {
	info.ConstraintUsage = make([]fdw.IndexConstraintUsage, len(info.Constraints))
	info.EstimatedCost = 1e12
	info.EstimatedRows = 1_000_000
	for i, constraint := range info.Constraints {
		if constraint.Column == 2 && constraint.Op == fdw.OpEQ && constraint.Usable {
			info.ConstraintUsage[i] = fdw.IndexConstraintUsage{ArgvIndex: 1, Omit: true}
			info.IdxNum = 1
			info.EstimatedCost = 1
			info.EstimatedRows = 1
			info.IdxFlags = fdw.IndexScanUnique
			break
		}
	}
	return nil
}

func (*browserHTTPSource) Open() (fdw.Cursor, error) { return &browserHTTPCursor{}, nil }
func (*browserHTTPSource) Disconnect() error         { return nil }
func (*browserHTTPSource) Destroy() error            { return nil }

type browserHTTPCursor struct {
	status int64
	body   string
	url    string
	done   bool
}

func (c *browserHTTPCursor) Filter(idxNum int, _ string, args []fdw.Value) error {
	c.done = false
	c.status = 0
	c.body = ""
	c.url = ""
	if idxNum != 1 || len(args) != 1 || args[0].Type() != fdw.Text {
		return errors.New("network_probe: add WHERE url = 'https://...' to the query")
	}

	c.url = args[0].Text()
	client := http.Client{Timeout: 10 * time.Second}
	resp, err := client.Get(c.url)
	if err != nil {
		return fmt.Errorf("network_probe: %w", err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(io.LimitReader(resp.Body, 64<<10))
	if err != nil {
		return fmt.Errorf("network_probe: read response: %w", err)
	}
	c.status = int64(resp.StatusCode)
	c.body = string(body)
	return nil
}

func (c *browserHTTPCursor) Next() error  { c.done = true; return nil }
func (c *browserHTTPCursor) EOF() bool    { return c.done }
func (c *browserHTTPCursor) Close() error { return nil }
func (c *browserHTTPCursor) RowID() (int64, error) {
	return 1, nil
}

func (c *browserHTTPCursor) Column(column int) (fdw.Value, error) {
	switch column {
	case 0:
		return fdw.IntValue(c.status), nil
	case 1:
		return fdw.TextValue(c.body), nil
	case 2:
		return fdw.TextValue(c.url), nil
	default:
		return fdw.NullValue(), nil
	}
}

func (s *workerState) close() {
	if s.db != nil {
		s.db.Close()
	}
}

func (s *workerState) handleRequest(raw string) {
	var req request
	if err := json.Unmarshal([]byte(raw), &req); err != nil {
		post(response{Type: "error", Error: "invalid request: " + err.Error()})
		return
	}
	switch req.Type {
	case "clone":
		s.handleClone(req)
	case "query":
		s.handleQuery(req)
	default:
		post(response{Type: "error", ID: req.ID, Error: "unknown request type"})
	}
}

func (s *workerState) handleClone(req request) {
	ctx, cancel := context.WithTimeout(context.Background(), cloneTimeout)
	defer cancel()
	repo, repoURL, err := cloneRepository(ctx, req)
	if err != nil {
		post(response{Type: "error", ID: req.ID, Error: err.Error()})
		return
	}
	post(response{Type: "progress", ID: req.ID, Message: "Registering Git virtual tables…"})
	db, err := openRepository(repo)
	if err != nil {
		post(response{Type: "error", ID: req.ID, Error: err.Error()})
		return
	}
	old := s.db
	s.db = db
	if old != nil {
		old.Close()
	}

	info := &repositoryInfo{URL: repoURL}
	if head, err := repo.Head(); err == nil {
		info.Head = head.Hash().String()
	}
	post(response{Type: "loaded", ID: req.ID, Repository: info})
}

func (s *workerState) handleQuery(req request) {
	if s.db == nil {
		post(response{Type: "error", ID: req.ID, Error: "load a repository before running SQL"})
		return
	}
	ctx, cancel := context.WithTimeout(context.Background(), queryTimeout)
	defer cancel()
	result, err := webquery.Run(ctx, s.db, req.SQL, maxResultRows)
	if err != nil {
		post(response{Type: "error", ID: req.ID, Error: err.Error()})
		return
	}
	post(response{Type: "result", ID: req.ID, Result: &result})
}

func post(value response) {
	data, err := json.Marshal(value)
	if err != nil {
		data = []byte(`{"type":"fatal","error":"response serialization failed"}`)
	}
	js.Global().Call("postMessage", string(data))
}

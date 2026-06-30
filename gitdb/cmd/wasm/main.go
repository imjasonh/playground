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
	"syscall/js"
	"time"

	"github.com/go-git/go-billy/v5"
	"github.com/go-git/go-billy/v5/memfs"
	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
	"github.com/go-git/go-git/v5/storage/memory"
	sqlite3 "github.com/ncruces/go-sqlite3"
	sqlite3driver "github.com/ncruces/go-sqlite3/driver"
	fdw "github.com/values-conflict/go-sqlite-fdw"
	ncrucesfdw "github.com/values-conflict/go-sqlite-fdw/ncruces"

	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
	"github.com/imjasonh/playground/gitdb/internal/tables"
	"github.com/imjasonh/playground/gitdb/internal/webquery"
)

const (
	demoSpec      = "demo"
	maxResultRows = 500
	queryTimeout  = 15 * time.Second
)

type request struct {
	Type string `json:"type"`
	ID   string `json:"id"`
	SQL  string `json:"sql"`
}

type response struct {
	Type   string           `json:"type"`
	ID     string           `json:"id,omitempty"`
	Error  string           `json:"error,omitempty"`
	Result *webquery.Result `json:"result,omitempty"`
}

func main() {
	db, err := openDemo()
	if err != nil {
		post(response{Type: "fatal", Error: err.Error()})
		return
	}
	defer db.Close()

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
	for raw := range inbox {
		handleRequest(db, raw)
	}
}

func openDemo() (*sql.DB, error) {
	repo, err := buildDemoRepository()
	if err != nil {
		return nil, fmt.Errorf("build demo repository: %w", err)
	}
	manager, err := gitrepo.NewManager(gitrepo.Options{CacheDir: "memory"})
	if err != nil {
		return nil, err
	}
	if err := manager.Bind(demoSpec, repo); err != nil {
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
	if err := tables.CreateAll(db, demoSpec); err != nil {
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

func buildDemoRepository() (*git.Repository, error) {
	repo, err := git.Init(memory.NewStorage(), memfs.New())
	if err != nil {
		return nil, err
	}
	worktree, err := repo.Worktree()
	if err != nil {
		return nil, err
	}

	alice := object.Signature{
		Name:  "Alice",
		Email: "alice@example.com",
		When:  time.Date(2021, 1, 1, 10, 0, 0, 0, time.UTC),
	}
	if err := writeAndAdd(worktree, "README.md", []byte("# Browser FDW demo\n\nSQLite meets git.\n")); err != nil {
		return nil, err
	}
	if err := writeAndAdd(worktree, "src.txt", []byte("alpha\nbeta\ngamma\n")); err != nil {
		return nil, err
	}
	first, err := worktree.Commit("build the demo", &git.CommitOptions{
		Author:    &alice,
		Committer: &alice,
	})
	if err != nil {
		return nil, err
	}

	bob := object.Signature{
		Name:  "Bob",
		Email: "bob@example.com",
		When:  time.Date(2021, 1, 2, 14, 30, 0, 0, time.FixedZone("UTC+5", 5*60*60)),
	}
	if err := writeAndAdd(worktree, "src.txt", []byte("alpha\nBETA\ngamma\ndelta\n")); err != nil {
		return nil, err
	}
	if err := writeAndAdd(worktree, "notes.txt", []byte("queried through a virtual table\n")); err != nil {
		return nil, err
	}
	if err := writeAndAdd(worktree, "binary.dat", []byte{0, 1, 2, 0}); err != nil {
		return nil, err
	}
	second, err := worktree.Commit("query git from SQLite", &git.CommitOptions{
		Author:    &bob,
		Committer: &bob,
	})
	if err != nil {
		return nil, err
	}

	if _, err := repo.CreateTag("v0.1", first, nil); err != nil {
		return nil, err
	}
	if _, err := repo.CreateTag("v0.2", second, &git.CreateTagOptions{
		Tagger:  &bob,
		Message: "browser spike\n",
	}); err != nil {
		return nil, err
	}
	if err := repo.Storer.SetReference(plumbing.NewHashReference(
		plumbing.NewBranchReferenceName("prototype"), first,
	)); err != nil {
		return nil, err
	}
	return repo, nil
}

func writeAndAdd(worktree *git.Worktree, name string, content []byte) error {
	if err := writeFile(worktree.Filesystem, name, content); err != nil {
		return err
	}
	_, err := worktree.Add(name)
	return err
}

func writeFile(fs billy.Filesystem, name string, content []byte) error {
	file, err := fs.Create(name)
	if err != nil {
		return err
	}
	_, writeErr := file.Write(content)
	return errors.Join(writeErr, file.Close())
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

func handleRequest(db *sql.DB, raw string) {
	var req request
	if err := json.Unmarshal([]byte(raw), &req); err != nil {
		post(response{Type: "error", Error: "invalid request: " + err.Error()})
		return
	}
	if req.Type != "query" {
		post(response{Type: "error", ID: req.ID, Error: "unknown request type"})
		return
	}

	ctx, cancel := context.WithTimeout(context.Background(), queryTimeout)
	defer cancel()
	result, err := webquery.Run(ctx, db, req.SQL, maxResultRows)
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

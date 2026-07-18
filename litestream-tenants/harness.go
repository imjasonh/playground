//go:build vfs

package main

import (
	"context"
	"database/sql"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/benbjohnson/litestream/file"
	_ "github.com/mattn/go-sqlite3"
	"github.com/psanford/sqlite3vfs"
)

// Harness owns a workspace of SQLite DBs replicated to a local file://
// Litestream tree (stand-in for GCS).
type Harness struct {
	Root       string
	SourceDir  string
	ReplicaDir string
	BufferDir  string
	RestoreDir string
	logger     *slog.Logger
	vfsSeq     atomic.Uint64
}

func NewHarness(root string) (*Harness, error) {
	h := &Harness{
		Root:       root,
		SourceDir:  filepath.Join(root, "source"),
		ReplicaDir: filepath.Join(root, "replicas"),
		BufferDir:  filepath.Join(root, "buffers"),
		RestoreDir: filepath.Join(root, "restored"),
		logger:     slog.Default(),
	}
	for _, d := range []string{h.SourceDir, h.ReplicaDir, h.BufferDir, h.RestoreDir} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			return nil, err
		}
	}
	return h, nil
}

func (h *Harness) sourcePath(name string) string {
	return filepath.Join(h.SourceDir, name+".db")
}

func (h *Harness) replicaPath(name string) string {
	return filepath.Join(h.ReplicaDir, name)
}

func (h *Harness) restorePath(name string) string {
	return filepath.Join(h.RestoreDir, name+".db")
}

func (h *Harness) replicateOnce(ctx context.Context, name, dbPath string) error {
	replicaPath := h.replicaPath(name)
	_ = os.RemoveAll(replicaPath)
	if err := os.MkdirAll(replicaPath, 0o755); err != nil {
		return err
	}
	client := file.NewReplicaClient(replicaPath)
	lsdb := litestream.NewDB(dbPath)
	lsdb.MonitorInterval = 0
	lsdb.Replica = litestream.NewReplicaWithClient(lsdb, client)
	lsdb.Replica.MonitorEnabled = false
	if err := lsdb.Open(); err != nil {
		return fmt.Errorf("litestream open %s: %w", name, err)
	}
	if err := lsdb.Sync(ctx); err != nil {
		_ = lsdb.Close(ctx)
		return fmt.Errorf("litestream sync db %s: %w", name, err)
	}
	if err := lsdb.Replica.Sync(ctx); err != nil {
		_ = lsdb.Close(ctx)
		return fmt.Errorf("litestream sync replica %s: %w", name, err)
	}
	return lsdb.Close(ctx)
}

// OpenMode selects how a DB is opened.
type OpenMode string

const (
	ModeLocal    OpenMode = "local"
	ModeVFSWrite OpenMode = "vfs-write"
	ModeVFSRead  OpenMode = "vfs-read"
	ModeRestore  OpenMode = "restore"
)

// DBHandle is an open connection plus cleanup.
type DBHandle struct {
	Name  string
	Mode  OpenMode
	DB    *sql.DB
	close func() error
}

func (t *DBHandle) Close() error {
	if t == nil {
		return nil
	}
	var err error
	if t.DB != nil {
		err = t.DB.Close()
	}
	if t.close != nil {
		if e := t.close(); e != nil && err == nil {
			err = e
		}
	}
	return err
}

func dsnLocal(path string) string {
	return path + "?_journal_mode=WAL&_busy_timeout=5000&_synchronous=NORMAL"
}

func (h *Harness) OpenDB(ctx context.Context, name string, mode OpenMode) (*DBHandle, time.Duration, error) {
	start := time.Now()
	switch mode {
	case ModeLocal:
		db, err := sql.Open("sqlite3", dsnLocal(h.sourcePath(name)))
		if err != nil {
			return nil, time.Since(start), err
		}
		db.SetMaxOpenConns(16)
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &DBHandle{Name: name, Mode: mode, DB: db}, time.Since(start), nil

	case ModeRestore:
		out := h.restorePath(name)
		_ = os.Remove(out)
		_ = os.Remove(out + "-wal")
		_ = os.Remove(out + "-shm")
		_ = os.RemoveAll(out + litestream.MetaDirSuffix)
		client := file.NewReplicaClient(h.replicaPath(name))
		lsdb := litestream.NewDB(out)
		lsdb.MonitorInterval = 0
		lsdb.Replica = litestream.NewReplicaWithClient(lsdb, client)
		lsdb.Replica.MonitorEnabled = false
		opt := litestream.NewRestoreOptions()
		opt.OutputPath = out
		if err := lsdb.Replica.Restore(ctx, opt); err != nil {
			return nil, time.Since(start), fmt.Errorf("restore %s: %w", name, err)
		}
		db, err := sql.Open("sqlite3", dsnLocal(out))
		if err != nil {
			return nil, time.Since(start), err
		}
		db.SetMaxOpenConns(8)
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &DBHandle{Name: name, Mode: mode, DB: db}, time.Since(start), nil

	case ModeVFSRead, ModeVFSWrite:
		client := file.NewReplicaClient(h.replicaPath(name))
		if err := client.Init(ctx); err != nil {
			return nil, time.Since(start), err
		}
		vfs := litestream.NewVFS(client, h.logger)
		vfs.PollInterval = 100 * time.Millisecond
		vfs.CacheSize = 32 << 20
		if mode == ModeVFSWrite {
			vfs.WriteEnabled = true
			vfs.WriteSyncInterval = 250 * time.Millisecond
			vfs.WriteBufferPath = filepath.Join(h.BufferDir, fmt.Sprintf("%s-%d.buf", name, h.vfsSeq.Add(1)))
		}
		vfsName := fmt.Sprintf("ls-%s-%d", name, h.vfsSeq.Add(1))
		if err := sqlite3vfs.RegisterVFS(vfsName, vfs); err != nil {
			return nil, time.Since(start), fmt.Errorf("register vfs: %w", err)
		}
		db, err := sql.Open("sqlite3", fmt.Sprintf("file:%s.db?vfs=%s&_busy_timeout=5000", name, vfsName))
		if err != nil {
			return nil, time.Since(start), err
		}
		// VFS write mode is single-writer; one connection avoids false TXID conflicts.
		if mode == ModeVFSWrite {
			db.SetMaxOpenConns(1)
		} else {
			db.SetMaxOpenConns(8)
		}
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &DBHandle{Name: name, Mode: mode, DB: db}, time.Since(start), nil

	default:
		return nil, time.Since(start), fmt.Errorf("unknown mode %q", mode)
	}
}

// DBPool lazily opens named DBs with an LRU cap.
type DBPool struct {
	h        *Harness
	mode     OpenMode
	capacity int
	mu       sync.Mutex
	order    []string
	open     map[string]*DBHandle
}

func NewDBPool(h *Harness, mode OpenMode, capacity int) *DBPool {
	if capacity < 1 {
		capacity = 1
	}
	return &DBPool{h: h, mode: mode, capacity: capacity, open: make(map[string]*DBHandle)}
}

func (p *DBPool) Get(ctx context.Context, name string) (*DBHandle, time.Duration, bool, error) {
	p.mu.Lock()
	if t, ok := p.open[name]; ok {
		p.touchLocked(name)
		p.mu.Unlock()
		return t, 0, true, nil
	}
	p.mu.Unlock()

	tdb, d, err := p.h.OpenDB(ctx, name, p.mode)
	if err != nil {
		return nil, d, false, err
	}

	p.mu.Lock()
	defer p.mu.Unlock()
	if existing, ok := p.open[name]; ok {
		_ = tdb.Close()
		p.touchLocked(name)
		return existing, d, true, nil
	}
	for len(p.open) >= p.capacity {
		evict := p.order[0]
		p.order = p.order[1:]
		if old := p.open[evict]; old != nil {
			_ = old.Close()
		}
		delete(p.open, evict)
	}
	p.open[name] = tdb
	p.order = append(p.order, name)
	return tdb, d, false, nil
}

func (p *DBPool) touchLocked(name string) {
	for i, t := range p.order {
		if t == name {
			p.order = append(p.order[:i], p.order[i+1:]...)
			break
		}
	}
	p.order = append(p.order, name)
}

func (p *DBPool) Close() {
	p.mu.Lock()
	defer p.mu.Unlock()
	for k, t := range p.open {
		_ = t.Close()
		delete(p.open, k)
	}
	p.order = nil
}

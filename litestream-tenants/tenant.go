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

// Harness owns a temp workspace of per-tenant SQLite DBs replicated to a
// local file:// Litestream replica tree (stand-in for GCS).
type Harness struct {
	Root       string
	SourceDir  string
	ReplicaDir string
	BufferDir  string
	RestoreDir string
	logger     *slog.Logger

	vfsSeq atomic.Uint64
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

func (h *Harness) TenantSourcePath(tenant string) string {
	return filepath.Join(h.SourceDir, tenant+".db")
}

func (h *Harness) TenantReplicaPath(tenant string) string {
	return filepath.Join(h.ReplicaDir, tenant)
}

func (h *Harness) TenantRestorePath(tenant string) string {
	return filepath.Join(h.RestoreDir, tenant+".db")
}

// SeedTenant creates a local SQLite DB for tenant, fills it, and replicates
// once to the file replica (simulating Litestream → GCS).
func (h *Harness) SeedTenant(ctx context.Context, tenant string, rows int, payloadBytes int) (int64, error) {
	if rows < 1 {
		rows = 1
	}
	if payloadBytes < 0 {
		payloadBytes = 0
	}
	path := h.TenantSourcePath(tenant)
	_ = os.Remove(path)
	_ = os.Remove(path + "-wal")
	_ = os.Remove(path + "-shm")

	db, err := sql.Open("sqlite3", path+"?_journal_mode=WAL&_busy_timeout=5000")
	if err != nil {
		return 0, err
	}
	if _, err := db.ExecContext(ctx, `
		PRAGMA synchronous=NORMAL;
		CREATE TABLE IF NOT EXISTS kv (
			id INTEGER PRIMARY KEY,
			payload BLOB NOT NULL
		);
	`); err != nil {
		_ = db.Close()
		return 0, err
	}

	payload := make([]byte, payloadBytes)
	for i := range payload {
		payload[i] = byte(i % 251)
	}

	tx, err := db.BeginTx(ctx, nil)
	if err != nil {
		_ = db.Close()
		return 0, err
	}
	stmt, err := tx.PrepareContext(ctx, `INSERT INTO kv(id, payload) VALUES(?, ?)`)
	if err != nil {
		_ = tx.Rollback()
		_ = db.Close()
		return 0, err
	}
	for i := 0; i < rows; i++ {
		if _, err := stmt.ExecContext(ctx, i, payload); err != nil {
			_ = stmt.Close()
			_ = tx.Rollback()
			_ = db.Close()
			return 0, err
		}
	}
	_ = stmt.Close()
	if err := tx.Commit(); err != nil {
		_ = db.Close()
		return 0, err
	}
	if err := db.Close(); err != nil {
		return 0, err
	}

	fi, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	size := fi.Size()
	if err := h.replicateOnce(ctx, tenant, path); err != nil {
		return size, err
	}
	return size, nil
}

func (h *Harness) replicateOnce(ctx context.Context, tenant, dbPath string) error {
	replicaPath := h.TenantReplicaPath(tenant)
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
		return fmt.Errorf("litestream open %s: %w", tenant, err)
	}
	if err := lsdb.Sync(ctx); err != nil {
		_ = lsdb.Close(ctx)
		return fmt.Errorf("litestream sync db %s: %w", tenant, err)
	}
	if err := lsdb.Replica.Sync(ctx); err != nil {
		_ = lsdb.Close(ctx)
		return fmt.Errorf("litestream sync replica %s: %w", tenant, err)
	}
	if err := lsdb.Close(ctx); err != nil {
		return err
	}
	return nil
}

// OpenMode selects how a tenant DB is opened for a bench.
type OpenMode string

const (
	ModeVFSWrite OpenMode = "vfs-write"
	ModeVFSRead  OpenMode = "vfs-read"
	ModeRestore  OpenMode = "restore"
	ModeLocal    OpenMode = "local" // already-seeded source file
)

// TenantDB is an open connection plus cleanup for one tenant.
type TenantDB struct {
	Tenant string
	Mode   OpenMode
	DB     *sql.DB
	close  func() error
}

func (t *TenantDB) Close() error {
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

// OpenTenant opens a tenant DB using the selected mode.
// For restore mode, OutputPath is rewritten each call (full restore).
func (h *Harness) OpenTenant(ctx context.Context, tenant string, mode OpenMode) (*TenantDB, time.Duration, error) {
	start := time.Now()
	switch mode {
	case ModeLocal:
		db, err := sql.Open("sqlite3", h.TenantSourcePath(tenant)+"?_journal_mode=WAL&_busy_timeout=5000&_query_only=false")
		if err != nil {
			return nil, time.Since(start), err
		}
		db.SetMaxOpenConns(16)
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &TenantDB{Tenant: tenant, Mode: mode, DB: db}, time.Since(start), nil

	case ModeRestore:
		out := h.TenantRestorePath(tenant)
		_ = os.Remove(out)
		_ = os.Remove(out + "-wal")
		_ = os.Remove(out + "-shm")
		_ = os.RemoveAll(out + litestream.MetaDirSuffix)

		client := file.NewReplicaClient(h.TenantReplicaPath(tenant))
		lsdb := litestream.NewDB(out)
		lsdb.MonitorInterval = 0
		lsdb.Replica = litestream.NewReplicaWithClient(lsdb, client)
		lsdb.Replica.MonitorEnabled = false

		opt := litestream.NewRestoreOptions()
		opt.OutputPath = out
		if err := lsdb.Replica.Restore(ctx, opt); err != nil {
			return nil, time.Since(start), fmt.Errorf("restore %s: %w", tenant, err)
		}
		db, err := sql.Open("sqlite3", out+"?_journal_mode=WAL&_busy_timeout=5000")
		if err != nil {
			return nil, time.Since(start), err
		}
		db.SetMaxOpenConns(8)
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &TenantDB{Tenant: tenant, Mode: mode, DB: db}, time.Since(start), nil

	case ModeVFSRead, ModeVFSWrite:
		client := file.NewReplicaClient(h.TenantReplicaPath(tenant))
		if err := client.Init(ctx); err != nil {
			return nil, time.Since(start), err
		}
		vfs := litestream.NewVFS(client, h.logger)
		vfs.PollInterval = 100 * time.Millisecond
		vfs.CacheSize = 32 << 20 // 32 MiB
		if mode == ModeVFSWrite {
			vfs.WriteEnabled = true
			vfs.WriteSyncInterval = 250 * time.Millisecond
			buf := filepath.Join(h.BufferDir, fmt.Sprintf("%s-%d.buf", tenant, h.vfsSeq.Add(1)))
			vfs.WriteBufferPath = buf
		}
		name := fmt.Sprintf("ls-%s-%d", tenant, h.vfsSeq.Add(1))
		if err := sqlite3vfs.RegisterVFS(name, vfs); err != nil {
			return nil, time.Since(start), fmt.Errorf("register vfs: %w", err)
		}
		dsn := fmt.Sprintf("file:%s.db?vfs=%s", tenant, name)
		db, err := sql.Open("sqlite3", dsn)
		if err != nil {
			return nil, time.Since(start), err
		}
		// VFS write mode coordinates a single writer; keep pool small.
		if mode == ModeVFSWrite {
			db.SetMaxOpenConns(1)
		} else {
			db.SetMaxOpenConns(8)
		}
		if err := db.PingContext(ctx); err != nil {
			_ = db.Close()
			return nil, time.Since(start), err
		}
		return &TenantDB{Tenant: tenant, Mode: mode, DB: db}, time.Since(start), nil

	default:
		return nil, time.Since(start), fmt.Errorf("unknown mode %q", mode)
	}
}

// TenantPool lazily opens tenant DBs (VFS write by default) and keeps an LRU
// of hot tenants — models on-demand writers without restoring every DB at boot.
type TenantPool struct {
	h        *Harness
	mode     OpenMode
	capacity int

	mu    sync.Mutex
	order []string
	open  map[string]*TenantDB
}

func NewTenantPool(h *Harness, mode OpenMode, capacity int) *TenantPool {
	if capacity < 1 {
		capacity = 1
	}
	return &TenantPool{
		h:        h,
		mode:     mode,
		capacity: capacity,
		open:     make(map[string]*TenantDB),
	}
}

func (p *TenantPool) Get(ctx context.Context, tenant string) (*TenantDB, time.Duration, bool, error) {
	p.mu.Lock()
	if t, ok := p.open[tenant]; ok {
		p.touchLocked(tenant)
		p.mu.Unlock()
		return t, 0, true, nil
	}
	p.mu.Unlock()

	tdb, d, err := p.h.OpenTenant(ctx, tenant, p.mode)
	if err != nil {
		return nil, d, false, err
	}

	p.mu.Lock()
	defer p.mu.Unlock()
	if existing, ok := p.open[tenant]; ok {
		_ = tdb.Close()
		p.touchLocked(tenant)
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
	p.open[tenant] = tdb
	p.order = append(p.order, tenant)
	return tdb, d, false, nil
}

func (p *TenantPool) touchLocked(tenant string) {
	for i, t := range p.order {
		if t == tenant {
			p.order = append(p.order[:i], p.order[i+1:]...)
			break
		}
	}
	p.order = append(p.order, tenant)
}

func (p *TenantPool) Close() {
	p.mu.Lock()
	defer p.mu.Unlock()
	for k, t := range p.open {
		_ = t.Close()
		delete(p.open, k)
	}
	p.order = nil
}

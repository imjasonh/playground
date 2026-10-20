// Package store runs a SQLite database whose only durable copy is a
// Litestream replica in object storage. Pages are read on demand through the
// Litestream VFS, so opening the database costs a few object-store requests
// regardless of how big it is.
package store

import (
	"context"
	"database/sql"
	"errors"
	"fmt"
	"log/slog"
	"math/rand/v2"
	"path/filepath"
	"sync"
	"sync/atomic"
	"time"

	"github.com/benbjohnson/litestream"
	_ "github.com/benbjohnson/litestream/file"
	_ "github.com/benbjohnson/litestream/gs"
	_ "github.com/benbjohnson/litestream/s3"
	_ "github.com/mattn/go-sqlite3"
	"github.com/psanford/sqlite3vfs"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/litevfs"
)

// ErrClosed is returned by Write after Close.
var ErrClosed = errors.New("store closed")

// Config configures a Store.
type Config struct {
	// ReplicaURL is the Litestream replica: gs://bucket/path,
	// s3://bucket/path?endpoint=..., or file:///path.
	ReplicaURL string

	// Dir is instance-local scratch space for the write buffer and the
	// hydrated copy. On Cloud Run that is the in-memory filesystem.
	Dir string

	// Durable makes Write return only after its transaction is in object
	// storage. Otherwise Write returns after the local commit and the VFS
	// uploads on SyncInterval, so a crash can lose up to that much.
	Durable bool

	// SyncInterval is how often the VFS uploads committed pages in the
	// background.
	SyncInterval time.Duration

	// PollInterval is how often the VFS lists the replica for files written
	// by compaction or by another instance.
	PollInterval time.Duration

	// CacheSize is the VFS page cache size in bytes.
	CacheSize int

	// Hydrate downloads the whole database to Dir in the background and
	// serves reads from it once complete. It costs memory equal to the
	// database size on Cloud Run.
	Hydrate bool

	// CompactionLevels merges L0 files into larger files over time. Nil
	// disables compaction.
	CompactionLevels litestream.CompactionLevels

	// L0Retention is how long L0 files are kept after compaction into L1.
	L0Retention time.Duration

	// SnapshotPlanLen triggers a snapshot when opening the database would
	// read more than this many LTX files. Zero disables snapshots.
	SnapshotPlanLen int

	// SnapshotCheckInterval is how often to compute the restore plan.
	SnapshotCheckInterval time.Duration

	// MaxBatch caps how many queued writes share one transaction and upload.
	MaxBatch int

	// Logger receives store logs. VFSLogger receives Litestream VFS logs.
	Logger    *slog.Logger
	VFSLogger *slog.Logger
}

// DefaultConfig returns the defaults used by the server.
func DefaultConfig() Config {
	return Config{
		Durable:      true,
		SyncInterval: time.Second,
		PollInterval: time.Second,
		CacheSize:    64 << 20,
		CompactionLevels: litestream.CompactionLevels{
			{Level: 0},
			{Level: 1, Interval: 10 * time.Second},
			{Level: 2, Interval: 2 * time.Minute},
			{Level: 3, Interval: 30 * time.Minute},
		},
		L0Retention:           2 * time.Minute,
		SnapshotPlanLen:       16,
		SnapshotCheckInterval: time.Minute,
		MaxBatch:              256,
	}
}

// Store is a SQLite database backed by a Litestream replica.
type Store struct {
	cfg    Config
	log    *slog.Logger
	client *fencedClient
	dsn    string

	// mu guards db. Reads hold it shared; the committer holds it
	// exclusively while it reopens the database after a conflict.
	mu   sync.RWMutex
	db   *sql.DB
	file atomic.Pointer[litevfs.VFSFile]

	writes  chan *writeReq
	jobs    chan func()
	closing chan struct{}
	done    chan struct{}
	bg      sync.WaitGroup
	closed  atomic.Bool

	openDuration time.Duration
	opens        atomic.Int64
	reopens      atomic.Int64
	writeCount   atomic.Int64
	batchCount   atomic.Int64
	flushes      latencies
	snapshotMu   sync.Mutex
	snapshots    atomic.Int64
	lastSnapshot atomic.Pointer[SnapshotResult]
}

type writeReq struct {
	ctx  context.Context
	fn   func(*sql.Tx) error
	done chan error
}

var vfsSeq atomic.Int64

// Open opens the database, creating it in the replica if it doesn't exist.
func Open(ctx context.Context, cfg Config) (*Store, error) {
	if cfg.Logger == nil {
		cfg.Logger = slog.Default()
	}
	if cfg.VFSLogger == nil {
		cfg.VFSLogger = cfg.Logger
	}
	if cfg.MaxBatch <= 0 {
		cfg.MaxBatch = 1
	}
	start := time.Now()

	raw, err := litestream.NewReplicaClientFromURL(cfg.ReplicaURL)
	if err != nil {
		return nil, fmt.Errorf("replica client: %w", err)
	}
	raw.SetLogger(cfg.VFSLogger)
	if err := raw.Init(ctx); err != nil {
		return nil, fmt.Errorf("init replica client: %w", err)
	}
	client, err := newFencedClient(ctx, raw)
	if err != nil {
		return nil, err
	}

	vfs := litevfs.NewVFS(client, cfg.VFSLogger)
	vfs.PollInterval = cfg.PollInterval
	vfs.CacheSize = cfg.CacheSize
	vfs.WriteEnabled = true
	vfs.WriteSyncInterval = cfg.SyncInterval
	vfs.WriteBufferPath = filepath.Join(cfg.Dir, "write-buffer")
	if cfg.Hydrate {
		vfs.HydrationEnabled = true
		vfs.HydrationPath = filepath.Join(cfg.Dir, "hydrated.db")
	}
	if cfg.CompactionLevels != nil {
		vfs.CompactionEnabled = true
		vfs.CompactionLevels = cfg.CompactionLevels
		vfs.L0Retention = cfg.L0Retention
	}

	s := &Store{
		cfg:     cfg,
		log:     cfg.Logger,
		client:  client,
		writes:  make(chan *writeReq),
		jobs:    make(chan func()),
		closing: make(chan struct{}),
		done:    make(chan struct{}),
	}
	name := fmt.Sprintf("litestream-%d", vfsSeq.Add(1))
	if err := sqlite3vfs.RegisterVFS(name, &captureVFS{VFS: vfs, store: s}); err != nil {
		return nil, fmt.Errorf("register VFS: %w", err)
	}
	s.dsn = fmt.Sprintf("file:db?vfs=%s&_busy_timeout=5000&_txlock=immediate", name)

	if s.db, err = s.openDB(ctx); err != nil {
		return nil, err
	}
	s.openDuration = time.Since(start)

	go s.commitLoop()
	if cfg.SnapshotPlanLen > 0 && cfg.SnapshotCheckInterval > 0 {
		s.bg.Add(1)
		go s.snapshotLoop()
	}
	return s, nil
}

func (s *Store) openDB(ctx context.Context) (*sql.DB, error) {
	if err := s.client.warmUp(ctx); err != nil {
		s.log.Warn("prefetch for open failed", "error", err)
	}
	defer s.client.coolDown()

	db, err := sql.Open("sqlite3", s.dsn)
	if err != nil {
		return nil, err
	}
	// One connection means one VFS file: one page cache, one write buffer,
	// and reads that always see this instance's own writes.
	db.SetMaxOpenConns(1)
	db.SetMaxIdleConns(1)
	db.SetConnMaxLifetime(0)
	db.SetConnMaxIdleTime(0)
	if err := db.PingContext(ctx); err != nil {
		db.Close()
		return nil, fmt.Errorf("open database: %w", err)
	}
	s.opens.Add(1)
	return db, nil
}

// captureVFS records the main database file each time SQLite opens it, so
// the committer can upload it directly after a commit.
type captureVFS struct {
	*litevfs.VFS
	store *Store
}

func (v *captureVFS) Open(name string, flags sqlite3vfs.OpenFlag) (sqlite3vfs.File, sqlite3vfs.OpenFlag, error) {
	f, outFlags, err := v.VFS.Open(name, flags)
	v.capture(f, flags)
	return f, outFlags, err
}

func (v *captureVFS) OpenURI(name string, params map[string]string, flags sqlite3vfs.OpenFlag) (sqlite3vfs.File, sqlite3vfs.OpenFlag, error) {
	f, outFlags, err := v.VFS.OpenURI(name, params, flags)
	v.capture(f, flags)
	return f, outFlags, err
}

func (v *captureVFS) capture(f sqlite3vfs.File, flags sqlite3vfs.OpenFlag) {
	if lf, ok := f.(*litevfs.VFSFile); ok && flags&sqlite3vfs.OpenMainDB != 0 {
		v.store.file.Store(lf)
	}
}

// Read runs fn against the database. Reads see every write this instance
// has committed, including ones still being uploaded.
func (s *Store) Read(ctx context.Context, fn func(*sql.DB) error) error {
	s.mu.RLock()
	defer s.mu.RUnlock()
	if err := ctx.Err(); err != nil {
		return err
	}
	return fn(s.db)
}

// Write runs fn in a transaction shared with other concurrent writes. When
// the store is durable, Write returns nil only after the transaction is in
// object storage. An error from fn rolls back only fn's own changes.
func (s *Store) Write(ctx context.Context, fn func(*sql.Tx) error) error {
	req := &writeReq{ctx: ctx, fn: fn, done: make(chan error, 1)}
	select {
	case s.writes <- req:
	case <-s.closing:
		return ErrClosed
	case <-ctx.Done():
		return ctx.Err()
	}
	select {
	case err := <-req.done:
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

// maxConflictRetries bounds how often a batch reruns after another writer
// published first. Retries back off with jitter so that two instances
// writing at once both make progress.
const maxConflictRetries = 10

func (s *Store) commitLoop() {
	defer close(s.done)
	for {
		var batch []*writeReq
		select {
		case req := <-s.writes:
			batch = append(batch, req)
		case job := <-s.jobs:
			job()
			continue
		case <-s.closing:
			return
		}
	drain:
		for len(batch) < s.cfg.MaxBatch {
			select {
			case req := <-s.writes:
				batch = append(batch, req)
			default:
				break drain
			}
		}
		s.runBatch(batch)
	}
}

func (s *Store) runBatch(batch []*writeReq) {
	var results []error
	var err error
	for attempt := 1; ; attempt++ {
		results, err = s.commitBatch(batch)
		if err == nil || !errors.Is(err, litevfs.ErrConflict) || attempt == maxConflictRetries {
			break
		}
		// Another instance published a transaction this instance hadn't
		// seen. The local commit was never uploaded, so throw it away and
		// rerun the batch against the replica's current state.
		s.log.Warn("write conflict, reopening database", "attempt", attempt, "error", err)
		time.Sleep(time.Duration(rand.Int64N(int64(attempt) * int64(10*time.Millisecond))))
		if rerr := s.reopen(); rerr != nil {
			err = errors.Join(err, rerr)
			break
		}
	}
	s.batchCount.Add(1)
	for i, req := range batch {
		switch {
		case err != nil:
			req.done <- err
		default:
			if results[i] == nil {
				s.writeCount.Add(1)
			}
			req.done <- results[i]
		}
	}
}

func (s *Store) commitBatch(batch []*writeReq) ([]error, error) {
	ctx := context.Background()
	tx, err := s.db.BeginTx(ctx, nil)
	if err != nil {
		return nil, err
	}
	results := make([]error, len(batch))
	for i, req := range batch {
		if err := req.ctx.Err(); err != nil {
			results[i] = err
			continue
		}
		if _, err := tx.ExecContext(ctx, "SAVEPOINT w"); err != nil {
			tx.Rollback()
			return nil, err
		}
		if err := req.fn(tx); err != nil {
			results[i] = err
			if _, err := tx.ExecContext(ctx, "ROLLBACK TO w"); err != nil {
				tx.Rollback()
				return nil, err
			}
		}
		if _, err := tx.ExecContext(ctx, "RELEASE w"); err != nil {
			tx.Rollback()
			return nil, err
		}
	}
	if err := tx.Commit(); err != nil {
		return nil, err
	}
	if s.cfg.Durable {
		if err := s.flush(); err != nil {
			return nil, err
		}
	}
	return results, nil
}

// flush uploads committed pages that are not yet in the replica. It must
// not run during a write transaction, which the VFS would skip; the
// committer is the only writer, so it calls flush between transactions.
func (s *Store) flush() error {
	f := s.file.Load()
	if f == nil {
		return errors.New("database file not open")
	}
	start := time.Now()
	err := f.Sync(0)
	s.flushes.add(time.Since(start))
	return err
}

func (s *Store) reopen() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	// Close tries a final upload, which conflicts again; the VFS then
	// discards the unuploaded pages.
	_ = s.db.Close()
	db, err := s.openDB(context.Background())
	if err != nil {
		return fmt.Errorf("reopen: %w", err)
	}
	s.db = db
	s.reopens.Add(1)
	return nil
}

// do runs fn on the committer goroutine, between write transactions.
func (s *Store) do(ctx context.Context, fn func() error) error {
	errc := make(chan error, 1)
	select {
	case s.jobs <- func() { errc <- fn() }:
	case <-s.closing:
		return ErrClosed
	case <-ctx.Done():
		return ctx.Err()
	}
	select {
	case err := <-errc:
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

// Flush uploads everything committed so far.
func (s *Store) Flush(ctx context.Context) error {
	return s.do(ctx, s.flush)
}

// Close uploads everything committed and closes the database. Call it only
// after every Write has returned.
func (s *Store) Close() error {
	if !s.closed.CompareAndSwap(false, true) {
		return nil
	}
	close(s.closing)
	<-s.done
	s.bg.Wait()
	err := s.flush()
	s.mu.Lock()
	defer s.mu.Unlock()
	return errors.Join(err, s.db.Close())
}

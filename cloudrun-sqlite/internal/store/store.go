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
	"math/rand/v2"
	"path/filepath"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"github.com/benbjohnson/litestream"
	_ "github.com/benbjohnson/litestream/file"
	_ "github.com/benbjohnson/litestream/gs"
	_ "github.com/benbjohnson/litestream/gsgrpc"
	_ "github.com/benbjohnson/litestream/s3"
	"github.com/chainguard-dev/clog"
	_ "github.com/mattn/go-sqlite3"
	"github.com/psanford/sqlite3vfs"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
)

// ErrClosed is returned by Write after Close.
var ErrClosed = errors.New("store closed")

// ErrUnavailable is returned while the database is closed because the
// store couldn't reopen it after a failed upload. The next write or read
// tries to open it again.
var ErrUnavailable = errors.New("database unavailable")

// Config configures a Store.
type Config struct {
	// ReplicaURL is the Litestream replica: gcs-grpc://bucket/path,
	// gs://bucket/path, s3://bucket/path?endpoint=..., or file:///path.
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
}

// DefaultConfig returns the defaults used by the server. Polling costs list
// requests while an instance has CPU, so that interval stays long: a single
// writer doesn't need to poll for its own files, and L0 retention only needs
// one poll after each L1 compaction. The snapshot check is shorter. A minute
// of writes with a 5 minute check left 936 L0 files, and the next instance
// spent 1.6 s and 734 GETs opening them.
func DefaultConfig() Config {
	return Config{
		Durable:               true,
		SyncInterval:          time.Second,
		PollInterval:          30 * time.Second,
		CacheSize:             64 << 20,
		CompactionLevels:      litestream.DefaultCompactionLevels,
		L0Retention:           5 * time.Minute,
		SnapshotPlanLen:       16,
		SnapshotCheckInterval: 15 * time.Second,
		MaxBatch:              256,
	}
}

// Store is a SQLite database backed by a Litestream replica.
type Store struct {
	cfg    Config
	client *monitoredClient
	dsn    string

	// mu guards db. Reads hold it shared. When the store is durable, the
	// committer holds it exclusively from the start of each batch until the
	// batch is in the replica or thrown away, so reads never see a write
	// that could still be lost. db is nil after a failed reopen.
	mu   sync.RWMutex
	db   *sql.DB
	file atomic.Pointer[litestream.VFSFile]

	writes    chan *writeReq
	jobs      chan func()
	retryOpen chan struct{}
	closing   chan struct{}
	done      chan struct{}
	bg        sync.WaitGroup
	closed    atomic.Bool

	openDuration time.Duration
	opens        atomic.Int64
	reopens      atomic.Int64
	writeCount   atomic.Int64
	batchCount   atomic.Int64
	readWait     latencies
	readQuery    latencies
	writeQueue   latencies
	tx           latencies
	flushes      latencies
	writeAcks    latencies
	pagedIn      latencies
	coldReads    latencies
	snapshotMu   sync.Mutex
	snapshots    atomic.Int64
	lastSnapshot atomic.Pointer[SnapshotResult]
	planLen      atomic.Int64

	// hooks lets tests pause or fail the committer. Set it before the first
	// Write.
	hooks testHooks
}

// testHooks are points where tests pause the committer or make it fail.
type testHooks struct {
	// beforeUpload runs after a durable batch commits locally. An error
	// stands in for a failed upload.
	beforeUpload func() error
	// beforeOpen runs before each reopen. An error stands in for a failed
	// open.
	beforeOpen func() error
}

type writeReq struct {
	ctx      context.Context
	fn       func(*sql.Tx) error
	done     chan error
	enqueued time.Time
}

var vfsSeq atomic.Int64

// Open opens the database, creating it in the replica if it doesn't exist.
// Litestream's client and VFS take *slog.Logger, so Open passes the logger
// from ctx at that call. Later logs read the logger from the context again.
func Open(ctx context.Context, cfg Config) (*Store, error) {
	if cfg.MaxBatch <= 0 {
		cfg.MaxBatch = 1
	}
	start := time.Now()

	raw, err := litestream.NewReplicaClientFromURL(cfg.ReplicaURL)
	if err != nil {
		return nil, fmt.Errorf("replica client: %w", err)
	}
	l := clog.FromContext(ctx)
	raw.SetLogger(&l.Logger)
	if err := raw.Init(ctx); err != nil {
		return nil, fmt.Errorf("init replica client: %w", err)
	}
	client := &monitoredClient{ReplicaClient: raw}

	vfs := litestream.NewVFS(client, &l.Logger)
	vfs.OpenPrefetch = true
	vfs.PollInterval = cfg.PollInterval
	vfs.CacheSize = cfg.CacheSize
	vfs.WriteEnabled = true
	vfs.WriteSyncInterval = cfg.SyncInterval
	vfs.WriteBufferPath = filepath.Join(cfg.Dir, "write-buffer")
	// Conditional L0 creates are enabled on the replica client, and nothing here deletes
	// an L0 file younger than L0Retention, so a writer can skip the
	// conflict-check LIST for half of that, leaving room for clock skew.
	vfs.ConflictCheckInterval = cfg.L0Retention / 2
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
		cfg:       cfg,
		client:    client,
		writes:    make(chan *writeReq),
		jobs:      make(chan func()),
		retryOpen: make(chan struct{}, 1),
		closing:   make(chan struct{}),
		done:      make(chan struct{}),
	}
	s.planLen.Store(-1)
	vfs.PageReadHook = s.notePageRead
	name := fmt.Sprintf("litestream-%d", vfsSeq.Add(1))
	if err := sqlite3vfs.RegisterVFS(name, &captureVFS{VFS: vfs, store: s}); err != nil {
		return nil, fmt.Errorf("register VFS: %w", err)
	}
	s.dsn = fmt.Sprintf("file:db?vfs=%s&_busy_timeout=5000&_txlock=immediate", name)

	if s.db, err = s.openDB(ctx); err != nil {
		return nil, err
	}
	s.openDuration = time.Since(start)

	go s.commitLoop(ctx)
	if cfg.SnapshotPlanLen > 0 && cfg.SnapshotCheckInterval > 0 {
		s.bg.Add(1)
		go s.snapshotLoop(ctx)
	}
	return s, nil
}

func (s *Store) openDB(ctx context.Context) (*sql.DB, error) {
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
	*litestream.VFS
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
	if lf, ok := f.(*litestream.VFSFile); ok && flags&sqlite3vfs.OpenMainDB != 0 {
		v.store.file.Store(lf)
	}
}

// Read runs fn against the database. When the store is durable, fn sees
// only writes that are in the replica. A write that is uploading stays
// hidden, and Read does not wait for that upload. Read returns
// ErrUnavailable if the store couldn't reopen the database after a failed
// upload. When the store is not durable, fn sees every committed write,
// including ones not yet uploaded.
func (s *Store) Read(ctx context.Context, fn func(*sql.DB) error) (err error) {
	ctx, end := observe.Span(ctx, "store.read")
	defer func() { end(err) }()
	wait := time.Now()
	s.mu.RLock()
	s.note(ctx, &s.readWait, "read_wait", time.Since(wait))
	defer s.mu.RUnlock()
	if err = ctx.Err(); err != nil {
		return err
	}
	if s.db == nil {
		select {
		case s.retryOpen <- struct{}{}:
		default:
		}
		err = ErrUnavailable
		return err
	}
	query := time.Now()
	err = fn(s.db)
	s.note(ctx, &s.readQuery, "read_query", time.Since(query))
	return err
}

// Write runs fn in a transaction shared with other concurrent writes. When
// the store is durable, Write returns nil only after the transaction is in
// object storage. An error from fn rolls back only fn's own changes. fn must
// not call Read, which waits for the transaction fn is part of.
func (s *Store) Write(ctx context.Context, fn func(*sql.Tx) error) (err error) {
	ctx, end := observe.Span(ctx, "store.write")
	start := time.Now()
	defer func() {
		d := time.Since(start)
		result := "ok"
		if err != nil {
			result = "error"
		} else {
			s.writeAcks.add(d)
		}
		observe.Measure(ctx, observe.StoreWrite, d, "durable", strconv.FormatBool(s.cfg.Durable), "result", result)
		end(err)
	}()
	req := &writeReq{ctx: ctx, fn: fn, done: make(chan error, 1), enqueued: start}
	select {
	case s.writes <- req:
	case <-s.closing:
		err = ErrClosed
		return err
	case <-ctx.Done():
		err = ctx.Err()
		return err
	}
	select {
	case err = <-req.done:
		return err
	case <-ctx.Done():
		err = ctx.Err()
		return err
	}
}

// maxConflictRetries bounds how often a batch reruns after another writer
// published first. Two instances can each land dozens of writes during a
// deploy overlap, so the bound is above one such burst. Retries back off
// with jitter so both make progress.
const maxConflictRetries = 48

func (s *Store) commitLoop(ctx context.Context) {
	defer close(s.done)
	for {
		var batch []*writeReq
		select {
		case req := <-s.writes:
			batch = append(batch, req)
		case job := <-s.jobs:
			job()
			continue
		case <-s.retryOpen:
			s.mu.Lock()
			if err := s.openIfClosedLocked(ctx); err != nil {
				clog.FromContext(ctx).Warn("database still unavailable", "error", err)
			}
			s.mu.Unlock()
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

func (s *Store) note(ctx context.Context, l *latencies, phase string, d time.Duration) {
	l.add(d)
	observe.Measure(ctx, observe.StorePhase, d, "phase", phase)
}

// notePageRead records a page read through the VFS. A page from the
// replica is cold; one from the write overlay, the page cache, or the
// hydrated copy was paged in. SQLite reads through its own page cache
// first, so a page it holds never gets here.
func (s *Store) notePageRead(source litestream.PageReadSource, d time.Duration) {
	l, label := &s.pagedIn, "paged_in"
	if source == litestream.PageReadReplica {
		l, label = &s.coldReads, "cold"
	}
	l.add(d)
	observe.Measure(context.Background(), observe.VFSPageRead, d, "source", label)
}

func batchContext(batch []*writeReq) context.Context {
	if len(batch) == 0 || batch[0].ctx == nil {
		return context.Background()
	}
	// The caller's cancel must not abort a batch other requests have joined.
	return context.WithoutCancel(batch[0].ctx)
}

func (s *Store) runBatch(batch []*writeReq) {
	now := time.Now()
	for _, req := range batch {
		if !req.enqueued.IsZero() {
			s.note(req.ctx, &s.writeQueue, "write_queue", now.Sub(req.enqueued))
		}
	}
	var results []error
	var err error
	for attempt := 1; ; attempt++ {
		results, err = s.commitBatch(batch, attempt)
		if err == nil || !errors.Is(err, litestream.ErrConflict) || attempt == maxConflictRetries {
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

// commitBatch runs batch in one transaction. When the store is durable, it
// holds s.mu for the SQLite commit, then uploads with the lock released so
// reads of the previous transaction can proceed. The VFS hides the
// un-uploaded pages while that is happening. If the upload fails, the store
// takes s.mu again and reopens the database from the replica, which throws
// the local commit away, or keeps it if the upload landed after all.
func (s *Store) commitBatch(batch []*writeReq, attempt int) ([]error, error) {
	ctx := batchContext(batch)
	if !s.cfg.Durable {
		return s.runTx(ctx, batch)
	}
	s.mu.Lock()
	if err := s.openIfClosedLocked(ctx); err != nil {
		s.mu.Unlock()
		return nil, err
	}
	results, err := s.runTx(ctx, batch)
	if err != nil {
		s.mu.Unlock()
		return nil, err
	}
	if file := s.file.Load(); file != nil {
		file.SetDurableRead(true)
	}
	s.mu.Unlock()

	if h := s.hooks.beforeUpload; h != nil {
		err = h()
	}
	if err == nil {
		err = s.flush(ctx)
	}
	if errors.Is(err, litestream.ErrConflict) {
		// Another instance published a transaction this instance hadn't
		// seen. Back off with jitter so that two instances writing at once
		// both make progress, then rerun against the replica's state.
		// Readers still see the previous upload while this waits.
		clog.FromContext(ctx).Warn("write conflict, reopening database", "attempt", attempt, "error", err)
		time.Sleep(time.Duration(rand.Int64N(int64(attempt) * int64(10*time.Millisecond))))
	}

	s.mu.Lock()
	if file := s.file.Load(); file != nil {
		file.SetDurableRead(false)
	}
	if err == nil {
		s.mu.Unlock()
		return results, nil
	}
	if rerr := s.reopenLocked(ctx); rerr != nil {
		err = errors.Join(err, rerr)
	}
	s.mu.Unlock()
	return nil, err
}

func (s *Store) runTx(ctx context.Context, batch []*writeReq) (results []error, err error) {
	ctx, end := observe.Span(ctx, "store.tx")
	start := time.Now()
	defer func() {
		s.note(ctx, &s.tx, "tx", time.Since(start))
		end(err)
	}()
	var tx *sql.Tx
	tx, err = s.db.BeginTx(ctx, nil)
	if err != nil {
		return nil, err
	}
	results = make([]error, len(batch))
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
	return results, nil
}

// flush uploads committed pages that are not yet in the replica. It must
// not run during a write transaction, which the VFS would skip; the
// committer is the only writer, so it calls flush between transactions.
func (s *Store) flush(ctx context.Context) (err error) {
	f := s.file.Load()
	if f == nil {
		return errors.New("database file not open")
	}
	ctx, end := observe.Span(ctx, "store.flush")
	start := time.Now()
	defer func() {
		s.note(ctx, &s.flushes, "flush", time.Since(start))
		end(err)
	}()
	err = f.Sync(0)
	return err
}

// reopenLocked replaces the database with one opened from the replica. If
// the open fails, s.db stays nil until openIfClosedLocked succeeds. The
// caller holds s.mu exclusively.
func (s *Store) reopenLocked(ctx context.Context) error {
	// Close tries a final upload. If that fails too, the VFS discards the
	// pages it couldn't upload.
	_ = s.db.Close()
	s.db = nil
	s.file.Store(nil)
	return s.openIfClosedLocked(ctx)
}

// openIfClosedLocked opens the database if a reopen failed. The caller holds
// s.mu exclusively.
func (s *Store) openIfClosedLocked(ctx context.Context) error {
	if s.db != nil {
		return nil
	}
	if h := s.hooks.beforeOpen; h != nil {
		if err := h(); err != nil {
			return fmt.Errorf("reopen: %w", err)
		}
	}
	db, err := s.openDB(ctx)
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
	return s.do(ctx, func() error { return s.flush(ctx) })
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
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.db == nil {
		return nil
	}
	return errors.Join(s.flush(context.Background()), s.db.Close())
}

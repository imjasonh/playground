// Package store runs a DuckDB database whose only durable copy is in object
// storage. DuckDB reads and writes a local file. After each commit, the
// store uploads the bytes DuckDB appended to its write-ahead log as the
// next entry of a numbered log, and now and then it uploads the whole file
// as a new base. A new instance downloads the newest base and the entries
// after it, and DuckDB replays them when it opens the file. See replica.go
// for the object layout.
package store

import (
	"context"
	"crypto/rand"
	"crypto/sha256"
	"database/sql"
	"database/sql/driver"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	mrand "math/rand/v2"
	"net/url"
	"os"
	"path/filepath"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/duckdb/duckdb-go/v2"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/observe"
)

// ErrClosed is returned by Write after Close.
var ErrClosed = errors.New("store closed")

// ErrUnavailable is returned while the database is closed because the store
// couldn't reopen it after a failed upload. The next write or read tries to
// open it again.
var ErrUnavailable = errors.New("database unavailable")

// ErrReadOnly is returned by Write, Flush, and Snapshot on a read-only store.
var ErrReadOnly = errors.New("store is read-only")

// ErrConflict means another instance published the next log entry first.
// Write reruns the batch against the replica's state a bounded number of
// times before returning it.
var ErrConflict = errors.New("another instance published first")

// Config configures a Store.
type Config struct {
	// ReplicaURL is gs://bucket/path or file:///path.
	ReplicaURL string

	// ReadOnly follows the replica without writing to it. DuckDB opens the
	// database read-only. Open waits until a writer has created the
	// database. Reads see another instance's writes after PollInterval.
	ReadOnly bool

	// Dir is instance-local scratch space for the database file and its
	// WAL. On Cloud Run that is the in-memory filesystem, so the whole
	// database counts against the instance's memory.
	Dir string

	// Durable makes Write return only after its commit is in object
	// storage. Otherwise Write returns after the local commit and the store
	// uploads every SyncInterval, so a crash can lose up to that much.
	Durable bool

	// SyncInterval is how often a store that isn't durable uploads.
	SyncInterval time.Duration

	// PollInterval is how often a read-only store lists the replica for
	// new entries.
	PollInterval time.Duration

	// SnapshotMinEntries sets the smallest restore cost that triggers a
	// snapshot: this many entries' worth. Zero disables snapshots.
	SnapshotMinEntries int

	// SnapshotEntryCost is about how many bytes of base download one log
	// entry's GET costs at cold start: restore fetches 32 entries at a
	// time, and a 25 ms round trip at 100 MB/s is about 80 KB spread over
	// 32 GETs. The store uploads a new base once the entries, their
	// commits, and their bytes would cost as much to restore as the base,
	// so a cold start never takes much longer than twice the base's
	// download.
	SnapshotEntryCost int64

	// Retention is the youngest age at which superseded objects are
	// deleted. A writer that hasn't confirmed its position for half of
	// this lists the replica before it publishes, so it can't publish over
	// an entry that retention deleted.
	Retention time.Duration

	// MaxBatch caps how many queued writes share one transaction and upload.
	MaxBatch int

	// MemoryLimit is DuckDB's memory_limit, for example "256MB". Empty
	// leaves DuckDB's default.
	MemoryLimit string

	// Threads is DuckDB's thread count. Zero leaves DuckDB's default.
	Threads int
}

// DefaultConfig returns the defaults used by the server.
func DefaultConfig() Config {
	return Config{
		Durable:            true,
		SyncInterval:       time.Second,
		PollInterval:       30 * time.Second,
		SnapshotMinEntries: 128,
		SnapshotEntryCost:  64 << 10,
		Retention:          5 * time.Minute,
		MaxBatch:           256,
		MemoryLimit:        "256MB",
		Threads:            2,
	}
}

// Querier is what Read hands to its function: the database, or a
// transaction that sees only what is in the replica.
type Querier interface {
	ExecContext(ctx context.Context, query string, args ...any) (sql.Result, error)
	QueryContext(ctx context.Context, query string, args ...any) (*sql.Rows, error)
	QueryRowContext(ctx context.Context, query string, args ...any) *sql.Row
}

// local is what this instance's files hold relative to the replica.
type local struct {
	seq      uint64    // newest log entry in both the local files and the replica
	baseSeq  uint64    // log entry of the base the local file matches; 0 for none
	baseKey  string    // that base's object key; empty for none
	baseSize int64     // that base's size
	main     fileStamp // the main file's stamp while it matches the base
	walSent  int64     // bytes of the local WAL that are in the replica
	entries  int       // log entries after the base
	walBytes int64     // bytes in those entries
	commits  int       // commits in those entries; restored entries count as one each
	// confirmed is when the replica last had nothing after seq.
	confirmed time.Time
}

// fileStamp identifies the main file's contents. DuckDB rewrites one of
// its two database headers, in the file's first 12 KiB, at every
// checkpoint. With automatic checkpoints and optimistic writes off (see
// dsn), nothing else writes the main file. A modification time can't
// stand in: on Linux it has the kernel tick's resolution, a few
// milliseconds.
type fileStamp struct {
	size   int64
	header [sha256.Size]byte
}

func stamp(path string) (fileStamp, error) {
	f, err := os.Open(path)
	if errors.Is(err, os.ErrNotExist) {
		return fileStamp{}, nil
	}
	if err != nil {
		return fileStamp{}, err
	}
	defer f.Close()
	fi, err := f.Stat()
	if err != nil {
		return fileStamp{}, err
	}
	buf := make([]byte, 3*4096)
	n, err := io.ReadFull(f, buf)
	if err != nil && !errors.Is(err, io.ErrUnexpectedEOF) && !errors.Is(err, io.EOF) {
		return fileStamp{}, err
	}
	return fileStamp{size: fi.Size(), header: sha256.Sum256(buf[:n])}, nil
}

// pinnedTxs is how many transactions each durable commit pins for reads.
const pinnedTxs = 4

// pinned holds transactions that started before a commit that is still
// uploading. Durable reads take one from free until the upload finishes.
type pinned struct {
	free    chan *sql.Tx
	conns   []*sql.Conn
	txs     []*sql.Tx
	readers sync.WaitGroup
}

// close rolls the transactions back once the reads using them finish.
func (p *pinned) close() {
	p.readers.Wait()
	for _, tx := range p.txs {
		tx.Rollback()
	}
	for _, c := range p.conns {
		c.Close()
	}
}

// Store is a DuckDB database backed by a replica in object storage.
type Store struct {
	cfg    Config
	bucket *monitoredBucket

	// mu guards db, path, and ls. Reads hold it shared; replacing the
	// database holds it exclusively. Only the committer (or, read-only,
	// the follower) writes them, so it reads them without the lock. db is
	// nil after a failed reopen.
	mu   sync.RWMutex
	db   *sql.DB
	path string
	ls   local
	// lsMu guards writes to ls and reads from Stats. The committer (or,
	// read-only, the follower) is the only writer, so it reads ls without
	// it.
	lsMu sync.Mutex

	// gate orders reads on the database against installing view. A read
	// on the database holds it shared for the whole query, so once the
	// committer has installed view under the exclusive lock, no read
	// started before the commit is still running on the database.
	gate sync.RWMutex
	view *pinned
	// unpublished counts local commits since the last upload. Only the
	// committer uses it.
	unpublished int

	// unpinning counts pinned sets whose transactions are still being
	// rolled back. A checkpoint or closing the database waits for it.
	unpinning sync.WaitGroup

	writes    chan *writeReq
	jobs      chan func()
	retryOpen chan struct{}
	closing   chan struct{}
	done      chan struct{}
	refreshed chan struct{}
	bg        sync.WaitGroup
	closed    atomic.Bool
	gen       int

	openDuration time.Duration
	lastRestore  atomic.Pointer[RestoreResult]
	opens        atomic.Int64
	reopens      atomic.Int64
	conflicts    atomic.Int64
	writeCount   atomic.Int64
	batchCount   atomic.Int64
	refreshes    atomic.Int64
	readWait     latencies
	readQuery    latencies
	writeQueue   latencies
	tx           latencies
	publishes    latencies
	writeAcks    latencies
	snapshots    atomic.Int64
	lastSnapshot atomic.Pointer[SnapshotResult]

	// hooks lets tests pause or fail the committer. Set it before the first
	// Write.
	hooks testHooks
}

type testHooks struct {
	// beforeUpload runs after a durable batch commits locally. An error
	// stands in for a failed upload.
	beforeUpload func() error
}

type writeReq struct {
	ctx      context.Context // pasta:ignore go_context_field (the queued write carries its caller's context)
	fn       func(*sql.Tx) error
	done     chan error
	enqueued time.Time
}

// Open restores the database from the replica, or creates an empty one if
// the replica is empty. A read-only store waits until the replica has a
// database.
func Open(ctx context.Context, cfg Config) (*Store, error) {
	if cfg.MaxBatch <= 0 {
		cfg.MaxBatch = 1
	}
	start := time.Now()
	raw, err := objstore.Open(ctx, cfg.ReplicaURL)
	if err != nil {
		return nil, err
	}
	if err := os.MkdirAll(cfg.Dir, 0o755); err != nil {
		return nil, err
	}
	s := &Store{
		cfg:       cfg,
		bucket:    &monitoredBucket{Bucket: raw},
		writes:    make(chan *writeReq),
		jobs:      make(chan func()),
		retryOpen: make(chan struct{}, 1),
		closing:   make(chan struct{}),
		done:      make(chan struct{}),
		refreshed: make(chan struct{}, 1),
	}
	if cfg.ReadOnly {
		if err := s.waitForBase(ctx); err != nil {
			return nil, err
		}
	}
	s.path = s.nextPath()
	if err := s.restoreLocked(ctx); err != nil {
		return nil, err
	}
	if !cfg.ReadOnly && s.ls.baseKey == "" {
		if err := s.createBase(ctx); err != nil {
			s.db.Close()
			return nil, err
		}
	}
	s.openDuration = time.Since(start)
	if cfg.ReadOnly {
		go s.followLoop(ctx)
	} else {
		go s.commitLoop(ctx)
	}
	return s, nil
}

// createBase publishes the new, empty database as the replica's first base,
// so that every commit after it is a WAL entry. If another instance creates
// the first base at the same time, it restores that one instead.
func (s *Store) createBase(ctx context.Context) error {
	_, err := s.publishBase(ctx)
	if !errors.Is(err, ErrConflict) {
		return err
	}
	return s.restoreLocked(ctx)
}

// nextPath returns a fresh database path. A read-only store opens each new
// base in its own directory so that the old one can keep serving until the
// new one is open.
func (s *Store) nextPath() string {
	if !s.cfg.ReadOnly {
		return filepath.Join(s.cfg.Dir, "db.duckdb")
	}
	s.gen++
	return filepath.Join(s.cfg.Dir, fmt.Sprintf("replica-%d", s.gen), "db.duckdb")
}

func (s *Store) waitForBase(ctx context.Context) error {
	every := min(max(s.cfg.PollInterval, 50*time.Millisecond), time.Second)
	for {
		p, err := readPlan(ctx, s.bucket)
		if err == nil && !p.empty() {
			return nil
		}
		if err != nil {
			clog.FromContext(ctx).Warn("read replica", "error", err)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(every):
		}
	}
}

// dsn configures DuckDB so that only the store's own CHECKPOINT writes the
// main file, because WAL bytes replay only onto the exact file they were
// written against, and a changed file has to be uploaded whole. Automatic
// checkpoints are off. Optimistic writes, which put large appends straight
// into the main file before commit, are off, so those appends go to the
// WAL like any other. openDB also turns off the checkpoint at close.
func (s *Store) dsn() string {
	q := url.Values{
		"checkpoint_threshold":    {"1TB"},
		"enable_optimistic_write": {"false"},
		// Never download extensions at runtime: a cold start must not
		// depend on extensions.duckdb.org.
		"autoinstall_known_extensions": {"false"},
		"autoload_known_extensions":    {"false"},
		"enable_external_access":       {"false"},
	}
	if s.cfg.ReadOnly {
		q.Set("access_mode", "READ_ONLY")
	}
	if s.cfg.MemoryLimit != "" {
		q.Set("memory_limit", s.cfg.MemoryLimit)
	}
	if s.cfg.Threads > 0 {
		q.Set("threads", strconv.Itoa(s.cfg.Threads))
	}
	return s.path + "?" + q.Encode()
}

func (s *Store) openDB(ctx context.Context) (*sql.DB, error) {
	if err := os.MkdirAll(filepath.Dir(s.path), 0o755); err != nil {
		return nil, err
	}
	connector, err := duckdb.NewConnector(s.dsn(), func(conn driver.ExecerContext) error {
		_, err := conn.ExecContext(context.Background(), "PRAGMA disable_checkpoint_on_shutdown", nil)
		return err
	})
	if err != nil {
		return nil, fmt.Errorf("open database: %w", err)
	}
	db := sql.OpenDB(connector)
	db.SetMaxOpenConns(16)
	db.SetMaxIdleConns(16)
	db.SetConnMaxLifetime(0)
	db.SetConnMaxIdleTime(0)
	if err := db.PingContext(ctx); err != nil {
		db.Close()
		return nil, fmt.Errorf("open database: %w", err)
	}
	s.opens.Add(1)
	return db, nil
}

// restoreLocked replaces the local files with the replica's newest base and
// log and opens them. The caller holds s.mu exclusively, or is Open.
func (s *Store) restoreLocked(ctx context.Context) error {
	s.closeDB()
	start := time.Now()
	p, err := readPlan(ctx, s.bucket)
	if err != nil {
		return fmt.Errorf("read replica: %w", err)
	}
	walSize, err := restore(ctx, s.bucket, p, s.path)
	if err != nil {
		return fmt.Errorf("restore: %w", err)
	}
	main, err := stamp(s.path)
	if err != nil {
		return err
	}
	db, err := s.openDB(ctx)
	if err != nil {
		return err
	}
	s.db = db
	s.unpublished = 0
	s.setLocal(local{
		seq:       p.last(),
		baseSeq:   p.baseSeq,
		baseKey:   p.baseKey,
		baseSize:  p.baseSize,
		main:      main,
		walSent:   walSize,
		entries:   len(p.entries),
		commits:   len(p.entries),
		walBytes:  walSize,
		confirmed: time.Now(),
	})
	s.lastRestore.Store(&RestoreResult{
		Seq:       p.last(),
		BaseBytes: p.baseSize,
		Entries:   len(p.entries),
		WALBytes:  walSize,
		Millis:    float64(time.Since(start)) / float64(time.Millisecond),
	})
	return nil
}

// catchUpLocked discards local changes that aren't in the replica and
// brings the database up to the replica's newest entry. When the replica's
// base is still the one the local file matches, it truncates the local WAL
// to what was uploaded and appends the entries it's missing, instead of
// downloading the base again. The caller holds s.mu exclusively.
func (s *Store) catchUpLocked(ctx context.Context) error {
	s.closeDB()
	p, err := readPlan(ctx, s.bucket)
	if err != nil {
		return fmt.Errorf("read replica: %w", err)
	}
	main, err := stamp(s.path)
	if err != nil {
		return err
	}
	if p.empty() || p.baseKey != s.ls.baseKey || main != s.ls.main {
		return s.restoreLocked(ctx)
	}
	var missing []objstore.Object
	for _, o := range p.entries {
		if seq, _ := parseLogKey(o.Key); seq > s.ls.seq {
			missing = append(missing, o)
		}
	}
	payloads, err := fetchEntries(ctx, s.bucket, missing)
	if err != nil {
		return s.restoreLocked(ctx)
	}
	wal := s.path + ".wal"
	if err := os.Truncate(wal, s.ls.walSent); err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	walSize, err := appendWAL(wal, payloads)
	if err != nil {
		return err
	}
	db, err := s.openDB(ctx)
	if err != nil {
		return err
	}
	s.db = db
	ls := s.ls
	ls.seq = p.last()
	ls.walSent = walSize
	ls.entries = len(p.entries)
	ls.commits = len(p.entries)
	s.unpublished = 0
	ls.walBytes = walSize
	ls.confirmed = time.Now()
	s.setLocal(ls)
	s.reopens.Add(1)
	return nil
}

func (s *Store) setLocal(ls local) {
	s.lsMu.Lock()
	s.ls = ls
	s.lsMu.Unlock()
}

// Read runs fn against the database. When the store is durable, fn sees
// only commits that are in the replica: while a commit uploads, fn runs in
// a transaction that started before it, so Read doesn't wait for the
// upload. Read returns ErrUnavailable if the store couldn't reopen the
// database after a failed upload.
func (s *Store) Read(ctx context.Context, fn func(Querier) error) error {
	wait := time.Now()
	s.mu.RLock()
	defer s.mu.RUnlock()
	s.note(&s.readWait, "read_wait", time.Since(wait))
	if err := ctx.Err(); err != nil {
		return err
	}
	if s.db == nil {
		select {
		case s.retryOpen <- struct{}{}:
		default:
		}
		return ErrUnavailable
	}
	err := s.query(fn)
	if err != nil && ctx.Err() != nil {
		// DuckDB reports a canceled query as an interrupt.
		err = errors.Join(ctx.Err(), err)
	}
	return err
}

func (s *Store) query(fn func(Querier) error) error {
	s.gate.RLock()
	v := s.view
	if v == nil {
		start := time.Now()
		err := fn(s.db)
		s.gate.RUnlock()
		s.note(&s.readQuery, "read_query", time.Since(start))
		return err
	}
	v.readers.Add(1)
	s.gate.RUnlock()
	defer v.readers.Done()
	tx := <-v.free
	start := time.Now()
	err := fn(tx)
	s.note(&s.readQuery, "read_query", time.Since(start))
	v.free <- tx
	return err
}

// Write runs fn in a transaction shared with other concurrent writes. When
// the store is durable, Write returns nil only after the transaction is in
// object storage. DuckDB has no savepoints and aborts a transaction on any
// error, so when fn fails the store rolls the whole batch back and reruns
// the others without it: fn may run more than once, and must only change
// the database through tx. fn must not call Read.
func (s *Store) Write(ctx context.Context, fn func(*sql.Tx) error) (err error) {
	start := time.Now()
	defer func() {
		d := time.Since(start)
		result := "ok"
		if err != nil {
			result = "error"
		} else {
			s.writeAcks.add(d)
		}
		observe.Measure(observe.StoreWrite, d, "durable", strconv.FormatBool(s.cfg.Durable), "result", result)
	}()
	if s.cfg.ReadOnly {
		return ErrReadOnly
	}
	req := &writeReq{ctx: ctx, fn: fn, done: make(chan error, 1), enqueued: start}
	select {
	case s.writes <- req:
	case <-s.closing:
		return ErrClosed
	case <-ctx.Done():
		return ctx.Err()
	}
	select {
	case err = <-req.done:
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

// maxConflictRetries bounds how often a batch reruns after another writer
// published first.
const maxConflictRetries = 48

func (s *Store) commitLoop(ctx context.Context) {
	defer close(s.done)
	var upload <-chan time.Time
	if !s.cfg.Durable && s.cfg.SyncInterval > 0 {
		t := time.NewTicker(s.cfg.SyncInterval)
		defer t.Stop()
		upload = t.C
	}
	for {
		var batch []*writeReq
		select {
		case req := <-s.writes:
			batch = append(batch, req)
		case job := <-s.jobs:
			job()
			continue
		case <-upload:
			if err := s.publishOrCatchUp(ctx); err != nil {
				clog.FromContext(ctx).Warn("background upload", "error", err)
			}
			continue
		case <-s.retryOpen:
			s.mu.Lock()
			if s.db == nil {
				if err := s.catchUpLocked(ctx); err != nil {
					clog.FromContext(ctx).Warn("database still unavailable", "error", err)
				}
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
		if s.shouldSnapshot() {
			if _, err := s.snapshot(batchContext(batch)); err != nil {
				clog.FromContext(ctx).Warn("snapshot", "error", err)
			}
		}
	}
}

func (s *Store) note(l *latencies, phase string, d time.Duration) {
	l.add(d)
	observe.Measure(observe.StorePhase, d, "phase", phase)
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
		s.note(&s.writeQueue, "write_queue", now.Sub(req.enqueued))
	}
	var results []error
	var err error
	for attempt := 1; ; attempt++ {
		results, err = s.commitBatch(batch, attempt)
		if err == nil || !errors.Is(err, ErrConflict) || attempt == maxConflictRetries {
			break
		}
	}
	s.batchCount.Add(1)
	for i, req := range batch {
		if err != nil {
			req.done <- err
			continue
		}
		if results[i] == nil {
			s.writeCount.Add(1)
		}
		req.done <- results[i]
	}
}

// commitBatch commits the batch locally and, when the store is durable,
// publishes it. Reads use a transaction pinned before the commit until the
// upload finishes. If the upload fails, the store takes s.mu and catches up
// with the replica, which throws the local commit away, or keeps it if the
// upload landed after all.
func (s *Store) commitBatch(batch []*writeReq, attempt int) ([]error, error) {
	ctx := batchContext(batch)
	if s.db == nil {
		s.mu.Lock()
		err := s.catchUpLocked(ctx)
		s.mu.Unlock()
		if err != nil {
			return nil, errors.Join(ErrUnavailable, err)
		}
	}
	var pin *pinned
	if s.cfg.Durable {
		var err error
		if pin, err = s.pin(ctx); err != nil {
			return nil, err
		}
		s.gate.Lock()
		s.view = pin
		s.gate.Unlock()
	}
	unpin := func() {
		if pin == nil {
			return
		}
		s.gate.Lock()
		s.view = nil
		s.gate.Unlock()
		s.unpinning.Go(pin.close)
	}
	results, err := s.runTx(ctx, batch)
	if err != nil {
		unpin()
		return nil, err
	}
	if !s.cfg.Durable {
		return results, nil
	}
	if h := s.hooks.beforeUpload; h != nil {
		err = h()
	}
	var needBase bool
	if err == nil {
		needBase, _, err = s.pending()
	}
	if err == nil && needBase {
		// A checkpoint can't run while the pinned read is open, so reads
		// wait for this upload instead.
		s.mu.Lock()
		unpin()
		if _, err = s.publishBase(ctx); err != nil {
			if cerr := s.catchUpLocked(ctx); cerr != nil {
				err = errors.Join(err, cerr)
			}
		}
		s.mu.Unlock()
		if err != nil {
			return nil, err
		}
		return results, nil
	}
	if err == nil {
		err = s.publish(ctx)
	}
	if err == nil {
		unpin()
		return results, nil
	}
	if errors.Is(err, ErrConflict) {
		s.conflicts.Add(1)
		clog.FromContext(ctx).Warn("write conflict, catching up", "attempt", attempt, "error", err)
		// Back off with jitter so two instances writing at once both make
		// progress. Reads still see the previous upload meanwhile.
		time.Sleep(mrand.N(time.Duration(attempt) * 10 * time.Millisecond))
	}
	s.mu.Lock()
	unpin()
	if cerr := s.catchUpLocked(ctx); cerr != nil {
		err = errors.Join(err, cerr)
	}
	s.mu.Unlock()
	return nil, err
}

// pin starts transactions on their own connections and reads the
// database in each, so their snapshots predate the next commit. DuckDB
// starts a transaction's snapshot at its first read of the database, not at
// BEGIN.
func (s *Store) pin(ctx context.Context) (*pinned, error) {
	p := &pinned{free: make(chan *sql.Tx, pinnedTxs)}
	for range pinnedTxs {
		conn, err := s.db.Conn(ctx)
		if err != nil {
			p.close()
			return nil, err
		}
		p.conns = append(p.conns, conn)
		tx, err := conn.BeginTx(ctx, nil)
		if err != nil {
			p.close()
			return nil, err
		}
		p.txs = append(p.txs, tx)
		var n int
		if err := tx.QueryRowContext(ctx, "SELECT count(*) FROM duckdb_tables() WHERE database_name = current_database()").Scan(&n); err != nil {
			p.close()
			return nil, err
		}
		p.free <- tx
	}
	return p, nil
}

// closeDB waits for pinned transactions to roll back, then closes the
// database. The caller holds s.mu exclusively.
func (s *Store) closeDB() {
	s.unpinning.Wait()
	if s.db != nil {
		s.db.Close()
		s.db = nil
	}
}

// runTx runs the batch in one transaction. When a function fails, the
// transaction rolls back and reruns without it.
func (s *Store) runTx(ctx context.Context, batch []*writeReq) ([]error, error) {
	start := time.Now()
	defer func() { s.note(&s.tx, "tx", time.Since(start)) }()
	results := make([]error, len(batch))
	var pending []int
	for i, req := range batch {
		if err := req.ctx.Err(); err != nil {
			results[i] = err
			continue
		}
		pending = append(pending, i)
	}
	for len(pending) > 0 {
		tx, err := s.db.BeginTx(ctx, nil)
		if err != nil {
			return nil, err
		}
		failed := -1
		for j, i := range pending {
			if err := batch[i].fn(tx); err != nil {
				results[i] = err
				failed = j
				break
			}
		}
		if failed >= 0 {
			tx.Rollback()
			pending = append(pending[:failed], pending[failed+1:]...)
			continue
		}
		if err := tx.Commit(); err != nil {
			return nil, err
		}
		s.unpublished++
		break
	}
	return results, nil
}

// publish uploads whatever the local files have that the replica doesn't:
// the WAL bytes since the last upload as one log entry, or, if the main
// file changed or there is no base yet, a checkpointed copy as a new base.
// It runs on the committer between transactions.
func (s *Store) publish(ctx context.Context) error {
	start := time.Now()
	defer func() { s.note(&s.publishes, "flush", time.Since(start)) }()
	needBase, walSize, err := s.pending()
	if err != nil {
		return err
	}
	if needBase {
		_, err := s.publishBase(ctx)
		return err
	}
	if walSize == s.ls.walSent {
		return nil
	}
	if err := s.confirmPosition(ctx); err != nil {
		return err
	}
	data := make([]byte, 1+walSize-s.ls.walSent)
	data[0] = kindWAL
	f, err := os.Open(s.path + ".wal")
	if err != nil {
		return err
	}
	_, err = f.ReadAt(data[1:], s.ls.walSent)
	f.Close()
	if err != nil {
		return fmt.Errorf("read WAL: %w", err)
	}
	next := s.ls.seq + 1
	if err := createOrMatch(ctx, s.bucket, logKey(next), data); err != nil {
		if errors.Is(err, objstore.ErrExists) {
			return fmt.Errorf("%w: log entry %d", ErrConflict, next)
		}
		return err
	}
	ls := s.ls
	ls.seq = next
	ls.walBytes += walSize - ls.walSent
	ls.walSent = walSize
	ls.entries++
	ls.commits += max(s.unpublished, 1)
	s.unpublished = 0
	ls.confirmed = time.Now()
	s.setLocal(ls)
	return nil
}

// pending reports whether the local files need a new base, because the
// main file no longer matches the last one or the WAL shrank, and the WAL's
// size. Open publishes a base for an empty replica, and only the store's
// own checkpoints change the main file, so a commit needs a base only if
// DuckDB checkpointed on its own.
func (s *Store) pending() (bool, int64, error) {
	main, err := stamp(s.path)
	if err != nil {
		return false, 0, err
	}
	walSize, err := fileSize(s.path + ".wal")
	if err != nil {
		return false, 0, err
	}
	return s.ls.baseKey == "" || main != s.ls.main || walSize < s.ls.walSent, walSize, nil
}

// confirmPosition lists the replica for entries after this instance's
// newest when it hasn't confirmed its position for half of Retention. Until
// then, an entry another instance published after it can't have been
// deleted, so the conditional create catches it.
func (s *Store) confirmPosition(ctx context.Context) error {
	if time.Since(s.ls.confirmed) < s.cfg.Retention/2 {
		return nil
	}
	objs, err := s.bucket.List(ctx, logPrefix, logKey(s.ls.seq))
	if err != nil {
		return err
	}
	if len(objs) > 0 {
		return fmt.Errorf("%w: replica has %s", ErrConflict, objs[0].Key)
	}
	ls := s.ls
	ls.confirmed = time.Now()
	s.setLocal(ls)
	return nil
}

// SnapshotResult describes the last base the store uploaded.
type SnapshotResult struct {
	Seq    uint64  `json:"seq"`
	Bytes  int64   `json:"bytes"`
	Millis float64 `json:"ms"`
	// Deleted is how many superseded objects retention deleted.
	Deleted int `json:"deleted"`
}

// RestoreResult describes the last time the store downloaded the replica.
type RestoreResult struct {
	Seq       uint64  `json:"seq"`
	BaseBytes int64   `json:"base_bytes"`
	Entries   int     `json:"entries"`
	WALBytes  int64   `json:"wal_bytes"`
	Millis    float64 `json:"ms"`
}

// publishBase checkpoints the database, uploads the file, and publishes a
// log entry that names it. It must not run while a pinned read is open.
//
// A committed transaction that created, altered, or updated anything, or
// drew from a sequence, holds DuckDB's shared checkpoint lock until no
// older transaction is open, so publishBase holds the gate to wait out
// reads on the database and keep new ones from starting until the
// checkpoint is done. FORCE then waits for DuckDB to clean up the last
// commit instead of failing. The file doesn't change during the upload,
// so reads continue then.
func (s *Store) publishBase(ctx context.Context) (*SnapshotResult, error) {
	start := time.Now()
	s.unpinning.Wait()
	s.gate.Lock()
	cctx, cancel := context.WithTimeout(ctx, 30*time.Second)
	_, err := s.db.ExecContext(cctx, "FORCE CHECKPOINT")
	cancel()
	s.gate.Unlock()
	if err != nil {
		return nil, fmt.Errorf("checkpoint: %w", err)
	}
	if err := s.confirmPosition(ctx); err != nil {
		return nil, err
	}
	main, err := stamp(s.path)
	if err != nil {
		return nil, err
	}
	walSize, err := fileSize(s.path + ".wal")
	if err != nil {
		return nil, err
	}
	next := s.ls.seq + 1
	key := baseKey(next, nonce())
	f, err := os.Open(s.path)
	if err != nil {
		return nil, err
	}
	err = s.bucket.Create(ctx, key, f, main.size)
	f.Close()
	if err != nil {
		return nil, fmt.Errorf("upload base: %w", err)
	}
	entry := append([]byte{kindBase}, key...)
	if err := createOrMatch(ctx, s.bucket, logKey(next), entry); err != nil {
		if derr := s.bucket.Delete(context.WithoutCancel(ctx), key); derr != nil {
			clog.FromContext(ctx).Warn("delete unpublished base", "key", key, "error", derr)
		}
		if errors.Is(err, objstore.ErrExists) {
			return nil, fmt.Errorf("%w: log entry %d", ErrConflict, next)
		}
		return nil, err
	}
	prev := s.ls.baseSeq
	s.unpublished = 0
	s.setLocal(local{
		seq:       next,
		baseSeq:   next,
		baseKey:   key,
		baseSize:  main.size,
		main:      main,
		walSent:   walSize,
		confirmed: time.Now(),
	})
	res := &SnapshotResult{Seq: next, Bytes: main.size, Millis: float64(time.Since(start)) / float64(time.Millisecond)}
	if prev > 0 {
		res.Deleted = s.deleteBefore(ctx, prev)
	}
	s.snapshots.Add(1)
	s.lastSnapshot.Store(res)
	return res, nil
}

func nonce() string {
	b := make([]byte, 6)
	rand.Read(b)
	return hex.EncodeToString(b)
}

// deleteBefore deletes log entries and bases from before seq that are older
// than Retention. It keeps the previous base and its entries, so an
// instance that is restoring from them can finish.
func (s *Store) deleteBefore(ctx context.Context, seq uint64) int {
	cutoff := time.Now().Add(-s.cfg.Retention)
	n := 0
	for _, prefix := range []string{logPrefix, basePrefix} {
		objs, err := s.bucket.List(ctx, prefix, "")
		if err != nil {
			clog.FromContext(ctx).Warn("list for retention", "error", err)
			continue
		}
		for _, o := range objs {
			oseq, ok := parseLogKey(o.Key)
			if !ok {
				oseq, ok = parseBaseKey(o.Key)
			}
			if !ok || oseq >= seq || o.Created.After(cutoff) {
				continue
			}
			if err := s.bucket.Delete(ctx, o.Key); err != nil {
				clog.FromContext(ctx).Warn("delete superseded object", "key", o.Key, "error", err)
				continue
			}
			n++
		}
	}
	return n
}

// commitReplayCost is about how many bytes of base download replaying one
// commit costs at cold start. DuckDB replays about 12,000 small commits a
// second, or 80 µs each, which is 8 KiB at 100 MB/s. Replaying a large
// commit runs at hundreds of MB/s, so the WAL's bytes count once.
const commitReplayCost = 8 << 10

// shouldSnapshot estimates, in bytes of base download, what restoring the
// entries after the base costs, and uploads a new base once that reaches
// the base's size, or SnapshotMinEntries entries' worth for a small base.
func (s *Store) shouldSnapshot() bool {
	if s.cfg.SnapshotMinEntries <= 0 || s.db == nil || s.ls.entries == 0 {
		return false
	}
	cost := int64(s.ls.entries)*s.cfg.SnapshotEntryCost + int64(s.ls.commits)*commitReplayCost + s.ls.walBytes
	return cost >= max(s.ls.baseSize, int64(s.cfg.SnapshotMinEntries)*s.cfg.SnapshotEntryCost)
}

// snapshot uploads a new base. When the store isn't durable, it first
// publishes what's pending, so the base doesn't carry writes the log lacks.
func (s *Store) snapshot(ctx context.Context) (*SnapshotResult, error) {
	res, err := s.publishBase(ctx)
	if err != nil {
		s.mu.Lock()
		if cerr := s.catchUpLocked(ctx); cerr != nil {
			err = errors.Join(err, cerr)
		}
		s.mu.Unlock()
	}
	return res, err
}

// publishOrCatchUp publishes pending commits. If that fails, it discards
// them and catches up, as a durable write would have.
func (s *Store) publishOrCatchUp(ctx context.Context) error {
	if s.db == nil {
		return nil
	}
	err := s.publish(ctx)
	if err == nil {
		return nil
	}
	if errors.Is(err, ErrConflict) {
		s.conflicts.Add(1)
	}
	s.mu.Lock()
	if cerr := s.catchUpLocked(ctx); cerr != nil {
		err = errors.Join(err, cerr)
	}
	s.mu.Unlock()
	return err
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
	if s.cfg.ReadOnly {
		return ErrReadOnly
	}
	return s.do(ctx, func() error { return s.publishOrCatchUp(ctx) })
}

// Snapshot uploads the whole database as a new base now.
func (s *Store) Snapshot(ctx context.Context) (*SnapshotResult, error) {
	if s.cfg.ReadOnly {
		return nil, ErrReadOnly
	}
	var res *SnapshotResult
	err := s.do(ctx, func() error {
		if s.db == nil {
			return ErrUnavailable
		}
		if err := s.publishOrCatchUp(ctx); err != nil {
			return err
		}
		var err error
		res, err = s.snapshot(ctx)
		return err
	})
	return res, err
}

// Refreshed signals after a read-only store installs new entries.
func (s *Store) Refreshed() <-chan struct{} { return s.refreshed }

// followLoop polls the replica and installs new entries.
func (s *Store) followLoop(ctx context.Context) {
	defer close(s.done)
	every := s.cfg.PollInterval
	if every <= 0 {
		every = 30 * time.Second
	}
	t := time.NewTicker(every)
	defer t.Stop()
	for {
		select {
		case <-s.closing:
			return
		case <-t.C:
		}
		changed, err := s.refresh(ctx)
		if err != nil {
			if ctx.Err() != nil {
				return
			}
			clog.FromContext(ctx).Warn("refresh replica", "error", err)
			continue
		}
		if changed {
			s.refreshes.Add(1)
			select {
			case s.refreshed <- struct{}{}:
			default:
			}
		}
	}
}

// refresh installs entries published since the last refresh. DuckDB can't
// replay WAL into an open database, so it appends them to the local WAL and
// reopens. If one of them is a new base, or retention deleted an entry it
// needed, it restores the new base into a fresh directory and switches to
// it once open.
func (s *Store) refresh(ctx context.Context) (bool, error) {
	objs, err := s.bucket.List(ctx, logPrefix, logKey(s.ls.seq))
	if err != nil || len(objs) == 0 {
		return false, err
	}
	want := s.ls.seq + 1
	contiguous := true
	for _, o := range objs {
		if seq, ok := parseLogKey(o.Key); !ok || seq != want {
			contiguous = false
			break
		}
		want++
	}
	var payloads [][]byte
	if contiguous {
		payloads, err = fetchEntries(ctx, s.bucket, objs)
	}
	if !contiguous || errors.Is(err, errNewBase) || errors.Is(err, objstore.ErrNotFound) {
		return true, s.switchBase(ctx)
	}
	if err != nil {
		return false, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.closeDB()
	walSize, err := appendWAL(s.path+".wal", payloads)
	if err != nil {
		return false, err
	}
	if s.db, err = s.openDB(ctx); err != nil {
		return false, err
	}
	ls := s.ls
	ls.seq = want - 1
	ls.walSent = walSize
	ls.entries += len(payloads)
	ls.commits += len(payloads)
	s.setLocal(ls)
	return true, nil
}

func (s *Store) switchBase(ctx context.Context) error {
	old, oldPath := s.db, s.path
	next := &Store{cfg: s.cfg, bucket: s.bucket, path: s.nextPath()}
	if err := next.restoreLocked(ctx); err != nil {
		os.RemoveAll(filepath.Dir(next.path))
		return err
	}
	s.mu.Lock()
	s.db, s.path = next.db, next.path
	s.setLocal(next.ls)
	s.mu.Unlock()
	s.lastRestore.Store(next.lastRestore.Load())
	s.opens.Add(next.opens.Load())
	if old != nil {
		old.Close()
	}
	return os.RemoveAll(filepath.Dir(oldPath))
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
	var err error
	if !s.cfg.ReadOnly {
		err = s.publish(context.Background())
	}
	s.unpinning.Wait()
	return errors.Join(err, s.db.Close())
}

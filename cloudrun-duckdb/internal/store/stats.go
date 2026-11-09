package store

import (
	"context"
	"io"
	"slices"
	"sync"
	"time"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/observe"
)

// latencies keeps the most recent durations for percentile reporting.
type latencies struct {
	mu   sync.Mutex
	ring [4096]time.Duration
	n    int
}

func (l *latencies) add(d time.Duration) {
	l.mu.Lock()
	l.ring[l.n%len(l.ring)] = d
	l.n++
	l.mu.Unlock()
}

// Percentiles summarizes recent durations in milliseconds.
type Percentiles struct {
	Count int     `json:"count"`
	P50   float64 `json:"p50_ms"`
	P90   float64 `json:"p90_ms"`
	P99   float64 `json:"p99_ms"`
	Max   float64 `json:"max_ms"`
}

func (l *latencies) percentiles() Percentiles {
	l.mu.Lock()
	n := min(l.n, len(l.ring))
	ds := slices.Clone(l.ring[:n])
	total := l.n
	l.mu.Unlock()
	if len(ds) == 0 {
		return Percentiles{}
	}
	slices.Sort(ds)
	at := func(q float64) float64 {
		return float64(ds[int(q*float64(len(ds)-1))]) / float64(time.Millisecond)
	}
	return Percentiles{Count: total, P50: at(0.50), P90: at(0.90), P99: at(0.99), Max: at(1)}
}

// monitoredBucket times each object-storage call.
type monitoredBucket struct {
	objstore.Bucket
	gets, lists, puts latencies
}

func (b *monitoredBucket) observe(l *latencies, op string, start time.Time) {
	d := time.Since(start)
	l.add(d)
	observe.Measure(observe.ReplicaOperation, d, "op", op)
}

func (b *monitoredBucket) Get(ctx context.Context, key string) (io.ReadCloser, error) {
	defer b.observe(&b.gets, "get", time.Now())
	return b.Bucket.Get(ctx, key)
}

func (b *monitoredBucket) Create(ctx context.Context, key string, r io.Reader, size int64) error {
	defer b.observe(&b.puts, "put", time.Now())
	return b.Bucket.Create(ctx, key, r, size)
}

func (b *monitoredBucket) List(ctx context.Context, prefix, startAfter string) ([]objstore.Object, error) {
	defer b.observe(&b.lists, "list", time.Now())
	return b.Bucket.List(ctx, prefix, startAfter)
}

// Stats describes the store for the /stats endpoint and benchmarks.
type Stats struct {
	OpenMillis float64     `json:"open_ms"`
	Durable    bool        `json:"durable"`
	ReadOnly   bool        `json:"read_only"`
	Opens      int64       `json:"opens"`
	Reopens    int64       `json:"reopens"`
	Refreshes  int64       `json:"refreshes"`
	Conflicts  int64       `json:"conflicts"`
	Writes     int64       `json:"writes"`
	Batches    int64       `json:"batches"`
	ReadWait   Percentiles `json:"read_wait"`
	ReadQuery  Percentiles `json:"read_query"`
	WriteQueue Percentiles `json:"write_queue"`
	Tx         Percentiles `json:"tx"`
	Flush      Percentiles `json:"flush"`
	// Write is from the call to Write to its acknowledgement, for writes
	// that succeeded. When the store is durable, that includes the upload.
	Write Percentiles `json:"write"`
	GCS   GCSStats    `json:"gcs"`

	Seq          uint64          `json:"seq"`
	BaseSeq      uint64          `json:"base_seq"`
	BaseBytes    int64           `json:"base_bytes"`
	Entries      int             `json:"entries_since_base"`
	WALBytes     int64           `json:"wal_bytes_since_base"`
	Snapshots    int64           `json:"snapshots"`
	LastSnapshot *SnapshotResult `json:"last_snapshot,omitempty"`
	LastRestore  *RestoreResult  `json:"last_restore,omitempty"`
}

// GCSStats is how long replica reads, listings, and uploads took.
type GCSStats struct {
	Get  Percentiles `json:"get"`
	List Percentiles `json:"list"`
	Put  Percentiles `json:"put"`
}

// Stats reports counters and the replica position.
func (s *Store) Stats() Stats {
	s.lsMu.Lock()
	ls := s.ls
	s.lsMu.Unlock()
	return Stats{
		OpenMillis: float64(s.openDuration) / float64(time.Millisecond),
		Durable:    s.cfg.Durable,
		ReadOnly:   s.cfg.ReadOnly,
		Opens:      s.opens.Load(),
		Reopens:    s.reopens.Load(),
		Refreshes:  s.refreshes.Load(),
		Conflicts:  s.conflicts.Load(),
		Writes:     s.writeCount.Load(),
		Batches:    s.batchCount.Load(),
		ReadWait:   s.readWait.percentiles(),
		ReadQuery:  s.readQuery.percentiles(),
		WriteQueue: s.writeQueue.percentiles(),
		Tx:         s.tx.percentiles(),
		Flush:      s.publishes.percentiles(),
		Write:      s.writeAcks.percentiles(),
		GCS: GCSStats{
			Get:  s.bucket.gets.percentiles(),
			List: s.bucket.lists.percentiles(),
			Put:  s.bucket.puts.percentiles(),
		},
		Seq:          ls.seq,
		BaseSeq:      ls.baseSeq,
		BaseBytes:    ls.baseSize,
		Entries:      ls.entries,
		WALBytes:     ls.walBytes,
		Snapshots:    s.snapshots.Load(),
		LastSnapshot: s.lastSnapshot.Load(),
		LastRestore:  s.lastRestore.Load(),
	}
}

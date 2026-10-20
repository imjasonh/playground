package store

import (
	"context"
	"database/sql"
	"slices"
	"sync"
	"time"
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
	return summarize(ds, total)
}

func summarize(ds []time.Duration, total int) Percentiles {
	if len(ds) == 0 {
		return Percentiles{}
	}
	slices.Sort(ds)
	at := func(q float64) float64 {
		return float64(ds[int(q*float64(len(ds)-1))]) / float64(time.Millisecond)
	}
	return Percentiles{Count: total, P50: at(0.50), P90: at(0.90), P99: at(0.99), Max: at(1)}
}

// Stats describes the store for the /stats endpoint and benchmarks.
type Stats struct {
	OpenMillis float64     `json:"open_ms"`
	Durable    bool        `json:"durable"`
	Opens      int64       `json:"opens"`
	Reopens    int64       `json:"reopens"`
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
	Write        Percentiles     `json:"write"`
	VFSRead      VFSReadStats    `json:"vfs_read"`
	GCS          GCSStats        `json:"gcs"`
	TXID         string          `json:"txid"`
	Hydration    string          `json:"hydration_pct,omitempty"`
	Snapshots    int64           `json:"snapshots"`
	LastSnapshot *SnapshotResult `json:"last_snapshot,omitempty"`
	// RestorePlanLen is the plan length at the last snapshot check, or -1
	// before the first one.
	RestorePlanLen int64 `json:"restore_plan_len"`
}

// VFSReadStats is how long SQLite's page reads through the VFS took. A
// paged-in page came from memory or the hydrated copy, and a cold one from
// the replica.
type VFSReadStats struct {
	PagedIn Percentiles `json:"paged_in"`
	Cold    Percentiles `json:"cold"`
}

// GCSStats is how long replica reads, listings, and uploads took.
type GCSStats struct {
	Get  Percentiles `json:"get"`
	List Percentiles `json:"list"`
	Put  Percentiles `json:"put"`
}

// Stats reports counters and queries the VFS for its position.
func (s *Store) Stats(ctx context.Context) Stats {
	st := Stats{
		OpenMillis: float64(s.openDuration) / float64(time.Millisecond),
		Durable:    s.cfg.Durable,
		Opens:      s.opens.Load(),
		Reopens:    s.reopens.Load(),
		Conflicts:  s.client.conflicts.Load(),
		Writes:     s.writeCount.Load(),
		Batches:    s.batchCount.Load(),
		ReadWait:   s.readWait.percentiles(),
		ReadQuery:  s.readQuery.percentiles(),
		WriteQueue: s.writeQueue.percentiles(),
		Tx:         s.tx.percentiles(),
		Flush:      s.flushes.percentiles(),
		Write:      s.writeAcks.percentiles(),
		VFSRead: VFSReadStats{
			PagedIn: s.pagedIn.percentiles(),
			Cold:    s.coldReads.percentiles(),
		},
		GCS: GCSStats{
			Get:  s.client.gets.percentiles(),
			List: s.client.lists.percentiles(),
			Put:  s.client.puts.percentiles(),
		},
		Snapshots:      s.snapshots.Load(),
		LastSnapshot:   s.lastSnapshot.Load(),
		RestorePlanLen: s.planLen.Load(),
	}
	_ = s.Read(ctx, func(db *sql.DB) error {
		_ = db.QueryRowContext(ctx, "PRAGMA litestream_txid").Scan(&st.TXID)
		if s.cfg.Hydrate {
			_ = db.QueryRowContext(ctx, "PRAGMA litestream_hydration_progress").Scan(&st.Hydration)
		}
		return nil
	})
	return st
}

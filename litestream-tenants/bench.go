//go:build vfs

package main

import (
	"context"
	"database/sql"
	"fmt"
	"os"
	"sync"
	"time"
)

func countRows(ctx context.Context, db *sql.DB) (int, error) {
	var n int
	err := db.QueryRowContext(ctx, `SELECT COUNT(*) FROM kv`).Scan(&n)
	return n, err
}

func insertRow(ctx context.Context, db *sql.DB) error {
	_, err := db.ExecContext(ctx, `INSERT INTO kv(payload) VALUES(randomblob(32))`)
	return err
}

// BenchColdOpen compares full restore vs VFS open for each tenant size.
func BenchColdOpen(ctx context.Context, h *Harness, tenants []string) ([]Report, error) {
	var reports []Report
	for _, tenant := range tenants {
		// Measure full restore + ping + count
		restoreStats := &Stats{}
		tdb, openDur, err := h.OpenTenant(ctx, tenant, ModeRestore)
		if err != nil {
			restoreStats.Record(openDur, err)
		} else {
			t0 := time.Now()
			_, qerr := countRows(ctx, tdb.DB)
			restoreStats.Record(openDur+time.Since(t0), qerr)
			_ = tdb.Close()
			// Clean restore artifacts so next restore is cold.
			_ = os.Remove(h.TenantRestorePath(tenant))
		}
		r := restoreStats.Snapshot()
		r.Label = fmt.Sprintf("restore/%s", tenant)
		r.Duration = openDur
		reports = append(reports, r)
		fmt.Println(r)

		// Measure VFS write open + ping + count (no full download)
		vfsStats := &Stats{}
		vdb, vOpen, err := h.OpenTenant(ctx, tenant, ModeVFSWrite)
		if err != nil {
			vfsStats.Record(vOpen, err)
		} else {
			t0 := time.Now()
			_, qerr := countRows(ctx, vdb.DB)
			vfsStats.Record(vOpen+time.Since(t0), qerr)
			_ = vdb.Close()
		}
		vr := vfsStats.Snapshot()
		vr.Label = fmt.Sprintf("vfs-write/%s", tenant)
		vr.Duration = vOpen
		reports = append(reports, vr)
		fmt.Println(vr)
	}
	return reports, nil
}

// BenchRW runs one writer + N readers against a single tenant for duration.
func BenchRW(ctx context.Context, h *Harness, tenant string, mode OpenMode, readers int, duration time.Duration) (Report, Report, error) {
	tdb, _, err := h.OpenTenant(ctx, tenant, mode)
	if err != nil {
		return Report{}, Report{}, err
	}
	defer tdb.Close()

	wStats := &Stats{}
	rStats := &Stats{}
	ctx, cancel := context.WithTimeout(ctx, duration)
	defer cancel()

	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			if ctx.Err() != nil {
				return
			}
			t0 := time.Now()
			err := insertRow(ctx, tdb.DB)
			wStats.Record(time.Since(t0), err)
		}
	}()

	for i := 0; i < readers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				if ctx.Err() != nil {
					return
				}
				t0 := time.Now()
				_, err := countRows(ctx, tdb.DB)
				rStats.Record(time.Since(t0), err)
			}
		}()
	}
	wg.Wait()

	w := wStats.Snapshot()
	w.Label = fmt.Sprintf("write/%s/%s", mode, tenant)
	w.Duration = duration
	r := rStats.Snapshot()
	r.Label = fmt.Sprintf("read/%s/%s readers=%d", mode, tenant, readers)
	r.Duration = duration
	fmt.Println(w)
	fmt.Println(r)
	return w, r, nil
}

// BenchConflict opens two VFS writers on the same tenant replica and writes.
// Local INSERTs often succeed (buffered); conflicts surface when a writer
// closes/syncs against a replica advanced by the other writer.
func BenchConflict(ctx context.Context, h *Harness, tenant string, duration time.Duration) (Report, error) {
	stats := &Stats{}
	ctx, cancel := context.WithTimeout(ctx, duration)
	defer cancel()

	var wg sync.WaitGroup
	for i := 0; i < 2; i++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			for {
				if ctx.Err() != nil {
					return
				}
				tdb, _, err := h.OpenTenant(ctx, tenant, ModeVFSWrite)
				if err != nil {
					stats.Record(0, err)
					time.Sleep(50 * time.Millisecond)
					continue
				}
				t0 := time.Now()
				err = insertRow(ctx, tdb.DB)
				// Close forces a sync; that is where dual-writer conflicts appear.
				closeErr := tdb.Close()
				if err == nil {
					err = closeErr
				}
				stats.Record(time.Since(t0), err)
				time.Sleep(50 * time.Millisecond)
			}
		}(i)
	}
	wg.Wait()

	r := stats.Snapshot()
	r.Label = fmt.Sprintf("conflict/%s", tenant)
	r.Duration = duration
	fmt.Println(r)
	return r, nil
}

// BenchFanout walks many tenants through a bounded LRU pool, measuring
// cold-open vs cache-hit latency for on-demand writers.
func BenchFanout(ctx context.Context, h *Harness, tenants []string, mode OpenMode, capacity int, rounds int) (Report, error) {
	pool := NewTenantPool(h, mode, capacity)
	defer pool.Close()

	stats := &Stats{}
	cold := &Stats{}
	hot := &Stats{}

	if rounds < 1 {
		rounds = 1
	}
	start := time.Now()
	for round := 0; round < rounds; round++ {
		for _, tenant := range tenants {
			t0 := time.Now()
			tdb, openDur, cached, err := pool.Get(ctx, tenant)
			if err != nil {
				stats.Record(time.Since(t0), err)
				continue
			}
			_, qerr := countRows(ctx, tdb.DB)
			total := time.Since(t0)
			stats.Record(total, qerr)
			if cached {
				hot.Record(total, qerr)
			} else {
				cold.Record(openDur+total, qerr)
			}
			_ = insertRow(ctx, tdb.DB)
		}
	}
	elapsed := time.Since(start)

	r := stats.Snapshot()
	r.Label = fmt.Sprintf("fanout/%s capacity=%d tenants=%d", mode, capacity, len(tenants))
	r.Duration = elapsed
	fmt.Println(r)

	cr := cold.Snapshot()
	cr.Label = "fanout-cold-open"
	cr.Duration = elapsed
	fmt.Println(cr)

	hr := hot.Snapshot()
	hr.Label = "fanout-cache-hit"
	hr.Duration = elapsed
	fmt.Println(hr)

	return r, nil
}

// BenchShard simulates hashing tenants onto K exclusive writer shards
// (each shard is a pool with capacity=all-its-tenants). No cross-shard sharing.
//
// Prefer ModeLocal here: it models K Cloud Run services each with max-instances=1
// and local SQLite (+ Litestream replicate). Holding many concurrent VFS write
// handles in one process under rapid multi-tenant write churn can surface
// "database disk image is malformed" — treat multi-tenant VFS writers as
// open-on-demand (see fanout) rather than all-hot in one process.
func BenchShard(ctx context.Context, h *Harness, tenants []string, shards int, mode OpenMode, duration time.Duration) ([]Report, error) {
	if shards < 1 {
		shards = 1
	}
	if mode == "" {
		mode = ModeLocal
	}
	groups := make([][]string, shards)
	for i, t := range tenants {
		groups[i%shards] = append(groups[i%shards], t)
	}

	var reports []Report
	var mu sync.Mutex
	var wg sync.WaitGroup
	ctx, cancel := context.WithTimeout(ctx, duration)
	defer cancel()

	for i, group := range groups {
		if len(group) == 0 {
			continue
		}
		wg.Add(1)
		go func(shard int, group []string) {
			defer wg.Done()
			pool := NewTenantPool(h, mode, len(group))
			defer pool.Close()
			stats := &Stats{}
			idx := 0
			var loggedError sync.Once
			for {
				if ctx.Err() != nil {
					break
				}
				tenant := group[idx%len(group)]
				idx++
				tdb, _, _, err := pool.Get(ctx, tenant)
				if err != nil {
					loggedError.Do(func() { fmt.Printf("shard-%d get error: %v\n", shard, err) })
					stats.Record(0, err)
					continue
				}
				t0 := time.Now()
				err = insertRow(ctx, tdb.DB)
				if err != nil {
					loggedError.Do(func() { fmt.Printf("shard-%d insert error: %v\n", shard, err) })
				}
				stats.Record(time.Since(t0), err)
			}
			r := stats.Snapshot()
			r.Label = fmt.Sprintf("shard-%d/%s tenants=%d", shard, mode, len(group))
			r.Duration = duration
			mu.Lock()
			reports = append(reports, r)
			fmt.Println(r)
			mu.Unlock()
		}(i, group)
	}
	wg.Wait()
	return reports, nil
}

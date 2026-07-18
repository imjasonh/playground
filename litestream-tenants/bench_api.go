//go:build vfs

package main

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"
)

// APIBenchConfig drives the control + per-repo API workload.
type APIBenchConfig struct {
	Mode       OpenMode
	Duration   time.Duration
	Readers    int // goroutines doing repo reads (+ ACL)
	Writers    int // goroutines doing repo writes (+ ACL)
	ControlR   int // goroutines doing ACL-only reads
	ControlW   int // goroutines doing rare control writes
	RepoLRU    int
	ReadWriteMix bool // if true, writers also do reads between writes
}

func (c APIBenchConfig) withDefaults() APIBenchConfig {
	if c.Mode == "" {
		c.Mode = ModeLocal
	}
	if c.Duration <= 0 {
		c.Duration = 3 * time.Second
	}
	if c.Readers < 0 {
		c.Readers = 0
	}
	if c.Writers < 0 {
		c.Writers = 0
	}
	if c.ControlR < 0 {
		c.ControlR = 0
	}
	if c.ControlW < 0 {
		c.ControlW = 0
	}
	if c.RepoLRU < 1 {
		c.RepoLRU = 8
	}
	if c.Readers == 0 && c.Writers == 0 && c.ControlR == 0 && c.ControlW == 0 {
		c.Readers = 16
		c.Writers = 4
		c.ControlR = 8
		c.ControlW = 1
	}
	return c
}

// APIReports is the set of stats from BenchAPI.
type APIReports struct {
	ControlRead  Report
	ControlWrite Report
	RepoRead     Report // includes ACL lookup
	RepoWrite    Report // includes ACL lookup
	Denied       int64
}

// BenchAPI runs concurrent control and repo workloads. Every repo op performs
// AuthorizeRepo against the control DB first.
func BenchAPI(ctx context.Context, w *World, cfg APIBenchConfig) (APIReports, error) {
	cfg = cfg.withDefaults()
	if len(w.RepoIDs) == 0 || len(w.UserIDs) == 0 {
		return APIReports{}, fmt.Errorf("world has no repos/users")
	}

	// Control plane stays on local SQLite in the API process (always hot).
	// Only per-repo DBs use cfg.Mode (local vs VFS), matching the intended deploy.
	control, _, err := w.H.OpenDB(ctx, controlDBName, ModeLocal)
	if err != nil {
		return APIReports{}, fmt.Errorf("open control: %w", err)
	}
	defer control.Close()

	repos := NewDBPool(w.H, cfg.Mode, cfg.RepoLRU)
	defer repos.Close()

	// Pre-open repos into LRU so steady-state QPS isn't dominated by open.
	for i, rid := range w.RepoIDs {
		if i >= cfg.RepoLRU {
			break
		}
		if _, _, _, err := repos.Get(ctx, repoDBName(rid)); err != nil {
			return APIReports{}, err
		}
	}

	var (
		ctrlRead  Stats
		ctrlWrite Stats
		repoRead  Stats
		repoWrite Stats
		denied    atomic.Int64
	)

	ctx, cancel := context.WithTimeout(ctx, cfg.Duration)
	defer cancel()

	var wg sync.WaitGroup
	var rr atomic.Uint64

	nextRepo := func() int64 {
		i := rr.Add(1)
		return w.RepoIDs[int(i)%len(w.RepoIDs)]
	}
	nextUser := func() int64 {
		i := rr.Add(1)
		return w.UserIDs[int(i)%len(w.UserIDs)]
	}
	nextPR := func() int {
		i := rr.Add(1)
		return int(i%uint64(w.Cfg.PRsPerRepo)) + 1
	}

	for i := 0; i < cfg.ControlR; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ctx.Err() == nil {
				uid, rid := nextUser(), nextRepo()
				t0 := time.Now()
				_, ok, err := AuthorizeRepo(ctx, control.DB, uid, rid)
				if err == nil && !ok {
					denied.Add(1)
				}
				ctrlRead.Record(time.Since(t0), err)
			}
		}()
	}

	for i := 0; i < cfg.ControlW; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ctx.Err() == nil {
				uid, rid := nextUser(), nextRepo()
				t0 := time.Now()
				err := controlGrantAccess(ctx, control.DB, rid, uid)
				ctrlWrite.Record(time.Since(t0), err)
				time.Sleep(5 * time.Millisecond) // control writes are rare
			}
		}()
	}

	for i := 0; i < cfg.Readers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ctx.Err() == nil {
				uid, rid, prn := nextUser(), nextRepo(), nextPR()
				t0 := time.Now()
				_, ok, err := AuthorizeRepo(ctx, control.DB, uid, rid)
				if err != nil {
					repoRead.Record(time.Since(t0), err)
					continue
				}
				if !ok {
					denied.Add(1)
					repoRead.Record(time.Since(t0), nil) // counted as fast deny
					continue
				}
				h, _, _, err := repos.Get(ctx, repoDBName(rid))
				if err != nil {
					repoRead.Record(time.Since(t0), err)
					continue
				}
				_, err = readPR(ctx, h.DB, prn)
				repoRead.Record(time.Since(t0), err)
			}
		}()
	}

	for i := 0; i < cfg.Writers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ctx.Err() == nil {
				uid, rid, prn := nextUser(), nextRepo(), nextPR()
				t0 := time.Now()
				_, ok, err := AuthorizeRepo(ctx, control.DB, uid, rid)
				if err != nil {
					repoWrite.Record(time.Since(t0), err)
					continue
				}
				if !ok {
					denied.Add(1)
					repoWrite.Record(time.Since(t0), nil)
					continue
				}
				h, _, _, err := repos.Get(ctx, repoDBName(rid))
				if err != nil {
					repoWrite.Record(time.Since(t0), err)
					continue
				}
				err = writeComment(ctx, h.DB, prn, uid)
				repoWrite.Record(time.Since(t0), err)
				if cfg.ReadWriteMix {
					_, _ = readPR(ctx, h.DB, prn)
				}
			}
		}()
	}

	wg.Wait()

	out := APIReports{
		ControlRead:  ctrlRead.Snapshot(),
		ControlWrite: ctrlWrite.Snapshot(),
		RepoRead:     repoRead.Snapshot(),
		RepoWrite:    repoWrite.Snapshot(),
		Denied:       denied.Load(),
	}
	out.ControlRead.Label = "control-read/local"
	out.ControlRead.Duration = cfg.Duration
	out.ControlWrite.Label = "control-write/local"
	out.ControlWrite.Duration = cfg.Duration
	out.RepoRead.Label = fmt.Sprintf("repo-read+acl/%s repos=%d", cfg.Mode, len(w.RepoIDs))
	out.RepoRead.Duration = cfg.Duration
	out.RepoWrite.Label = fmt.Sprintf("repo-write+acl/%s repos=%d", cfg.Mode, len(w.RepoIDs))
	out.RepoWrite.Duration = cfg.Duration

	fmt.Println(out.ControlRead)
	fmt.Println(out.ControlWrite)
	fmt.Println(out.RepoRead)
	fmt.Println(out.RepoWrite)
	fmt.Printf("acl-denied=%d  effective_repo_read_qps_per_repo=%.1f  effective_repo_write_qps_per_repo=%.1f\n",
		out.Denied,
		out.RepoRead.RPS()/float64(len(w.RepoIDs)),
		out.RepoWrite.RPS()/float64(len(w.RepoIDs)),
	)
	return out, nil
}

// BenchRepoColdOpen compares restore vs VFS for a single seeded repo DB.
func BenchRepoColdOpen(ctx context.Context, w *World) error {
	if len(w.RepoIDs) == 0 {
		return fmt.Errorf("no repos")
	}
	name := repoDBName(w.RepoIDs[0])

	restoreStats := &Stats{}
	h, openDur, err := w.H.OpenDB(ctx, name, ModeRestore)
	if err != nil {
		restoreStats.Record(openDur, err)
	} else {
		t0 := time.Now()
		_, qerr := readPR(ctx, h.DB, 1)
		restoreStats.Record(openDur+time.Since(t0), qerr)
		_ = h.Close()
	}
	r := restoreStats.Snapshot()
	r.Label = "restore/" + name
	r.Duration = openDur
	fmt.Println(r)

	vfsStats := &Stats{}
	vh, vOpen, err := w.H.OpenDB(ctx, name, ModeVFSWrite)
	if err != nil {
		vfsStats.Record(vOpen, err)
	} else {
		t0 := time.Now()
		_, qerr := readPR(ctx, vh.DB, 1)
		vfsStats.Record(vOpen+time.Since(t0), qerr)
		_ = vh.Close()
	}
	vr := vfsStats.Snapshot()
	vr.Label = "vfs-write/" + name
	vr.Duration = vOpen
	fmt.Println(vr)
	return nil
}

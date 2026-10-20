package store

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"io"
	"slices"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/superfly/ltx"
)

// SnapshotResult describes a snapshot written by Snapshot.
type SnapshotResult struct {
	MaxTXID  string        `json:"max_txid"`
	Size     int64         `json:"size"`
	Inputs   int           `json:"inputs"`
	Deleted  int           `json:"deleted"`
	Duration time.Duration `json:"duration"`
	At       time.Time     `json:"at"`
}

// RestorePlan returns the LTX files a new instance would read to open the
// database: the latest snapshot plus the shortest chain of newer files.
func (s *Store) RestorePlan(ctx context.Context) ([]*ltx.FileInfo, error) {
	return litestream.CalcRestorePlan(ctx, s.client, 0, time.Time{}, s.log)
}

func (s *Store) snapshotLoop() {
	defer s.bg.Done()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	go func() {
		<-s.closing
		cancel()
	}()
	t := time.NewTicker(s.cfg.SnapshotCheckInterval)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		plan, err := s.RestorePlan(ctx)
		if err != nil || len(plan) <= s.cfg.SnapshotPlanLen {
			continue
		}
		if _, err := s.Snapshot(ctx); err != nil && ctx.Err() == nil {
			s.log.Error("snapshot failed", "error", err)
		}
	}
}

// Snapshot merges the restore plan into one snapshot file, so that new
// instances open the database by reading that file and whatever was written
// after it. It then deletes files that the previous snapshot already
// covered.
func (s *Store) Snapshot(ctx context.Context) (*SnapshotResult, error) {
	s.snapshotMu.Lock()
	defer s.snapshotMu.Unlock()
	start := time.Now()

	plan, err := s.RestorePlan(ctx)
	if err != nil {
		return nil, err
	}
	if len(plan) == 0 || (len(plan) == 1 && plan[0].Level == litestream.SnapshotLevel) {
		return nil, nil
	}
	if plan[0].MinTXID != 1 {
		return nil, fmt.Errorf("restore plan starts at TXID %s, not 1", plan[0].MinTXID)
	}

	info, err := s.writeSnapshot(ctx, plan)
	if err != nil {
		return nil, err
	}

	// Point this instance's page index at the new snapshot before deleting
	// anything it might still reference. The VFS only polls L0 and L1 for
	// new files, so it would never move off older files by itself.
	if err := s.do(ctx, func() error {
		if err := s.flush(); err != nil {
			return err
		}
		s.mu.RLock()
		defer s.mu.RUnlock()
		_, err := s.db.ExecContext(ctx, "PRAGMA litestream_time = 'latest'")
		return err
	}); err != nil {
		return nil, fmt.Errorf("reset page index: %w", err)
	}

	deleted, err := s.enforceRetention(ctx)
	if err != nil {
		s.log.Warn("retention failed", "error", err)
	}

	res := &SnapshotResult{
		MaxTXID:  info.MaxTXID.String(),
		Size:     info.Size,
		Inputs:   len(plan),
		Deleted:  deleted,
		Duration: time.Since(start),
		At:       time.Now(),
	}
	s.snapshots.Add(1)
	s.lastSnapshot.Store(res)
	s.log.Info("snapshot written", "max_txid", res.MaxTXID, "size", res.Size, "inputs", res.Inputs, "deleted", res.Deleted, "duration", res.Duration)
	return res, nil
}

func (s *Store) writeSnapshot(ctx context.Context, plan []*ltx.FileInfo) (*ltx.FileInfo, error) {
	rdrs := make([]io.Reader, 0, len(plan))
	defer func() {
		for _, r := range rdrs {
			r.(io.Closer).Close()
		}
	}()
	for _, info := range plan {
		rc, err := s.client.OpenLTXFile(ctx, info.Level, info.MinTXID, info.MaxTXID, 0, 0)
		if err != nil {
			return nil, fmt.Errorf("open %s: %w", ltx.FormatFilename(info.MinTXID, info.MaxTXID), err)
		}
		rdrs = append(rdrs, rc)
	}

	pr, pw := io.Pipe()
	comp, err := ltx.NewCompactor(pw, rdrs)
	if err != nil {
		return nil, err
	}
	comp.HeaderFlags = ltx.HeaderFlagNoChecksum
	go func() { pw.CloseWithError(comp.Compact(ctx)) }()

	maxTXID := plan[len(plan)-1].MaxTXID
	info, err := s.client.WriteLTXFile(ctx, litestream.SnapshotLevel, 1, maxTXID, pr)
	pr.CloseWithError(err)
	return info, err
}

// enforceRetention keeps the two newest snapshots and deletes every
// lower-level file that the older of the two already covers. Keeping one
// extra generation gives instances that opened before the newest snapshot
// time to finish; they may still read files the newest snapshot replaced.
func (s *Store) enforceRetention(ctx context.Context) (int, error) {
	snapshots, err := s.listLevel(ctx, litestream.SnapshotLevel)
	if err != nil {
		return 0, err
	}
	if len(snapshots) < 2 {
		return 0, nil
	}
	slices.SortFunc(snapshots, func(a, b *ltx.FileInfo) int { return cmp.Compare(a.MaxTXID, b.MaxTXID) })
	cutoff := snapshots[len(snapshots)-2].MaxTXID

	var victims []*ltx.FileInfo
	victims = append(victims, snapshots[:len(snapshots)-2]...)
	for level := 0; level < litestream.SnapshotLevel; level++ {
		infos, err := s.listLevel(ctx, level)
		if err != nil {
			return 0, err
		}
		for _, info := range infos {
			if info.MaxTXID <= cutoff {
				victims = append(victims, info)
			}
		}
	}
	if len(victims) == 0 {
		return 0, nil
	}
	var errs []error
	for chunk := range slices.Chunk(victims, 1000) {
		if err := s.client.DeleteLTXFiles(ctx, chunk); err != nil {
			errs = append(errs, err)
		}
	}
	return len(victims), errors.Join(errs...)
}

func (s *Store) listLevel(ctx context.Context, level int) ([]*ltx.FileInfo, error) {
	itr, err := s.client.LTXFiles(ctx, level, 0, false)
	if err != nil {
		return nil, err
	}
	defer itr.Close()
	var infos []*ltx.FileInfo
	for itr.Next() {
		info := *itr.Item()
		infos = append(infos, &info)
	}
	return infos, itr.Close()
}

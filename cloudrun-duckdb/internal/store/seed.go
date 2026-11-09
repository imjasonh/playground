package store

import (
	"context"
	"database/sql"
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
)

// ReadReplica restores the replica into a scratch directory, opens it
// read-only, and runs fn against it.
func (s *Store) ReadReplica(ctx context.Context, fn func(Querier) error) error {
	dir, err := os.MkdirTemp(s.cfg.Dir, "check-*")
	if err != nil {
		return err
	}
	defer os.RemoveAll(dir)
	cfg := s.cfg
	cfg.ReadOnly = true
	tmp := &Store{cfg: cfg, bucket: s.bucket, path: filepath.Join(dir, "db.duckdb")}
	if err := tmp.restoreLocked(ctx); err != nil {
		return err
	}
	defer tmp.db.Close()
	return fn(tmp.db)
}

// Seed replaces the replica with a database that fill builds, published as
// one base. Without force, it refuses a replica that has objects.
func Seed(ctx context.Context, cfg Config, force bool, fill func(context.Context, *sql.DB) error) (*SnapshotResult, error) {
	raw, err := objstore.Open(ctx, cfg.ReplicaURL)
	if err != nil {
		return nil, err
	}
	var existing []objstore.Object
	for _, prefix := range []string{logPrefix, basePrefix} {
		objs, err := raw.List(ctx, prefix, "")
		if err != nil {
			return nil, err
		}
		existing = append(existing, objs...)
	}
	if len(existing) > 0 && !force {
		return nil, fmt.Errorf("replica has %d objects; pass -force to replace them", len(existing))
	}
	for _, o := range existing {
		if err := raw.Delete(ctx, o.Key); err != nil {
			return nil, err
		}
	}
	if err := os.MkdirAll(cfg.Dir, 0o755); err != nil {
		return nil, err
	}
	s := &Store{cfg: cfg, bucket: &monitoredBucket{Bucket: raw}, path: filepath.Join(cfg.Dir, "seed.duckdb")}
	for _, f := range []string{s.path, s.path + ".wal"} {
		if err := os.Remove(f); err != nil && !errors.Is(err, os.ErrNotExist) {
			return nil, err
		}
	}
	defer os.Remove(s.path)
	defer os.Remove(s.path + ".wal")
	if s.db, err = s.openDB(ctx); err != nil {
		return nil, err
	}
	defer s.db.Close()
	if err := fill(ctx, s.db); err != nil {
		return nil, err
	}
	return s.publishBase(ctx)
}

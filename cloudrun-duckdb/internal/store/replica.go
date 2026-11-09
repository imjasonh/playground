package store

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
)

// The replica is a numbered log of commits and the database files they
// refer to:
//
//	log/<seq>              one commit: a kind byte, then its payload
//	base/<seq>-<nonce>.duckdb  a whole database file
//
// Sequence numbers are 16 hex digits, so keys sort in commit order. A
// commit is published by creating log/<seq> only if it doesn't exist, so
// two instances can't both publish the same sequence number.
//
// A 'W' entry's payload is the bytes DuckDB appended to its write-ahead
// log for that commit. A 'B' entry's payload is the key of a base file,
// uploaded just before the entry, that holds the database as of that
// commit. Restoring takes the newest base and appends every later entry's
// bytes to a WAL beside it; DuckDB replays that WAL when it opens the
// file. WAL bytes describe changes to one exact database file, so every
// entry after a base was written by an instance whose file was that base.
const (
	logPrefix  = "log/"
	basePrefix = "base/"
	kindWAL    = 'W'
	kindBase   = 'B'

	// fetchParallelism bounds concurrent GETs while restoring.
	fetchParallelism = 32
)

func logKey(seq uint64) string { return fmt.Sprintf("%s%016x", logPrefix, seq) }

func parseLogKey(key string) (uint64, bool) {
	s, ok := strings.CutPrefix(key, logPrefix)
	if !ok || len(s) != 16 {
		return 0, false
	}
	n, err := strconv.ParseUint(s, 16, 64)
	return n, err == nil
}

func baseKey(seq uint64, nonce string) string {
	return fmt.Sprintf("%s%016x-%s.duckdb", basePrefix, seq, nonce)
}

func parseBaseKey(key string) (uint64, bool) {
	s, ok := strings.CutPrefix(key, basePrefix)
	if !ok || len(s) < 17 || s[16] != '-' {
		return 0, false
	}
	n, err := strconv.ParseUint(s[:16], 16, 64)
	return n, err == nil
}

// errNoBase means the replica has log entries but none of them has a base
// file, which the protocol never produces.
var errNoBase = errors.New("replica has log entries but no base")

// plan is what restoring the replica reads: the newest base and the log
// entries after it.
type plan struct {
	baseSeq  uint64 // 0 when the replica is empty
	baseKey  string
	baseSize int64
	entries  []objstore.Object // contiguous, starting at baseSeq+1
}

func (p *plan) last() uint64 {
	if len(p.entries) == 0 {
		return p.baseSeq
	}
	seq, _ := parseLogKey(p.entries[len(p.entries)-1].Key)
	return seq
}

func (p *plan) empty() bool { return p.baseKey == "" }

// readPlan lists the replica and finds the newest base that its log entry
// confirms. A base without that entry is left over from a publish that lost
// a race or crashed, and is skipped.
func readPlan(ctx context.Context, b objstore.Bucket) (*plan, error) {
	var logs, bases []objstore.Object
	var lerr, berr error
	var wg sync.WaitGroup
	wg.Go(func() { logs, lerr = b.List(ctx, logPrefix, "") })
	wg.Go(func() { bases, berr = b.List(ctx, basePrefix, "") })
	wg.Wait()
	if err := errors.Join(lerr, berr); err != nil {
		return nil, err
	}
	seqs := map[uint64]int{}
	for i, o := range logs {
		if seq, ok := parseLogKey(o.Key); ok {
			seqs[seq] = i
		}
	}
	slices.SortFunc(bases, func(a, b objstore.Object) int { return strings.Compare(b.Key, a.Key) })
	p := &plan{}
	for _, base := range bases {
		seq, ok := parseBaseKey(base.Key)
		if !ok {
			continue
		}
		if _, ok := seqs[seq]; !ok {
			continue
		}
		entry, err := objstore.ReadAll(ctx, b, logKey(seq))
		if errors.Is(err, objstore.ErrNotFound) {
			continue
		}
		if err != nil {
			return nil, err
		}
		if len(entry) > 0 && entry[0] == kindBase && string(entry[1:]) == base.Key {
			p.baseSeq, p.baseKey, p.baseSize = seq, base.Key, base.Size
			break
		}
	}
	if p.empty() {
		if len(seqs) > 0 {
			return nil, errNoBase
		}
		return p, nil
	}
	want := p.baseSeq + 1
	for _, o := range logs {
		seq, ok := parseLogKey(o.Key)
		if !ok || seq <= p.baseSeq {
			continue
		}
		if seq != want {
			return nil, fmt.Errorf("replica log has a gap: want entry %d, found %d", want, seq)
		}
		p.entries = append(p.entries, o)
		want++
	}
	return p, nil
}

// fetchEntries gets log entries in parallel and returns their payloads in
// order. Each must be a WAL entry.
func fetchEntries(ctx context.Context, b objstore.Bucket, entries []objstore.Object) ([][]byte, error) {
	out := make([][]byte, len(entries))
	errs := make([]error, len(entries))
	sem := make(chan struct{}, fetchParallelism)
	var wg sync.WaitGroup
	for i, o := range entries {
		sem <- struct{}{}
		wg.Go(func() {
			defer func() { <-sem }()
			data, err := objstore.ReadAll(ctx, b, o.Key)
			switch {
			case err != nil:
				errs[i] = err
			case len(data) == 0 || data[0] != kindWAL:
				errs[i] = errNewBase
			default:
				out[i] = data[1:]
			}
		})
	}
	wg.Wait()
	return out, errors.Join(errs...)
}

// errNewBase means a log entry being fetched is a base, so the caller has
// to restore from it instead of appending.
var errNewBase = errors.New("log entry is a base")

// restore writes the plan's base to dbPath and its entries to dbPath.wal,
// replacing both, and returns the WAL's size.
func restore(ctx context.Context, b objstore.Bucket, p *plan, dbPath string) (int64, error) {
	if err := os.MkdirAll(filepath.Dir(dbPath), 0o755); err != nil {
		return 0, err
	}
	for _, f := range []string{dbPath, dbPath + ".wal"} {
		if err := os.Remove(f); err != nil && !errors.Is(err, os.ErrNotExist) {
			return 0, err
		}
	}
	if p.empty() {
		return 0, nil
	}
	var payloads [][]byte
	var perr error
	var wg sync.WaitGroup
	wg.Go(func() { payloads, perr = fetchEntries(ctx, b, p.entries) })
	derr := download(ctx, b, p.baseKey, dbPath)
	wg.Wait()
	if err := errors.Join(derr, perr); err != nil {
		return 0, err
	}
	return appendWAL(dbPath+".wal", payloads)
}

func download(ctx context.Context, b objstore.Bucket, key, path string) error {
	rc, err := b.Get(ctx, key)
	if err != nil {
		return fmt.Errorf("get %s: %w", key, err)
	}
	defer rc.Close()
	tmp := path + ".download"
	f, err := os.Create(tmp)
	if err != nil {
		return err
	}
	if _, err := io.Copy(f, rc); err != nil {
		f.Close()
		os.Remove(tmp)
		return fmt.Errorf("get %s: %w", key, err)
	}
	if err := f.Close(); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}

// appendWAL appends payloads to the file at path and returns its new size.
func appendWAL(path string, payloads [][]byte) (int64, error) {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0o644)
	if err != nil {
		return 0, err
	}
	for _, p := range payloads {
		if _, err := f.Write(p); err != nil {
			f.Close()
			return 0, err
		}
	}
	if err := f.Close(); err != nil {
		return 0, err
	}
	return fileSize(path)
}

func fileSize(path string) (int64, error) {
	fi, err := os.Stat(path)
	if errors.Is(err, os.ErrNotExist) {
		return 0, nil
	}
	if err != nil {
		return 0, err
	}
	return fi.Size(), nil
}

// createOrMatch creates key with data. If the key exists with exactly data,
// an earlier attempt of this same call landed, and it reports success.
func createOrMatch(ctx context.Context, b objstore.Bucket, key string, data []byte) error {
	err := b.Create(ctx, key, bytes.NewReader(data), int64(len(data)))
	if !errors.Is(err, objstore.ErrExists) {
		return err
	}
	got, gerr := objstore.ReadAll(ctx, b, key)
	if gerr == nil && bytes.Equal(got, data) {
		return nil
	}
	return err
}

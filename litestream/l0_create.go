package litestream

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"time"

	"github.com/superfly/ltx"
)

// ErrLTXObjectExists means a conditional level-0 create found an object at the
// key. Replica clients use it internally; callers see ErrConflict when the
// existing object is not a byte-for-byte retry of the same upload.
var ErrLTXObjectExists = errors.New("ltx object already exists")

// L0CreateOnlyReplicaClient is implemented by replica clients that can make
// level-0 writes create-if-absent instead of overwriting.
type L0CreateOnlyReplicaClient interface {
	ReplicaClient
	SetL0CreateOnly(enabled bool)
	L0CreateOnly() bool
	L0ConflictCount() int64
}

// SetReplicaL0CreateOnly enables or disables conditional create-if-absent for
// level-0 writes. It returns an error when the client does not support it.
func SetReplicaL0CreateOnly(c ReplicaClient, enabled bool) error {
	cc, ok := c.(L0CreateOnlyReplicaClient)
	if !ok {
		if enabled {
			return fmt.Errorf("replica type %q does not support conditional L0 writes", c.Type())
		}
		return nil
	}
	cc.SetL0CreateOnly(enabled)
	return nil
}

// ReplicaL0ConflictCount reports how many conditional L0 creates lost to
// another writer. It returns zero when the client does not track conflicts.
func ReplicaL0ConflictCount(c ReplicaClient) int64 {
	cc, ok := c.(L0CreateOnlyReplicaClient)
	if !ok {
		return 0
	}
	return cc.L0ConflictCount()
}

// CompleteL0CreateOnly finishes a level-0 write after createFn reports
// ErrLTXObjectExists. When the object already there matches data, the upload
// is treated as a successful idempotent retry.
func CompleteL0CreateOnly(ctx context.Context, client ReplicaClient, minTXID, maxTXID ltx.TXID, data []byte, ts time.Time, onConflict func()) (*ltx.FileInfo, error) {
	rc, err := client.OpenLTXFile(ctx, 0, minTXID, maxTXID, 0, 0)
	if err != nil {
		if onConflict != nil {
			onConflict()
		}
		return nil, fmt.Errorf("%w: another writer already published L0 %s", ErrConflict, ltx.FormatFilename(minTXID, maxTXID))
	}
	defer rc.Close()
	existing, err := io.ReadAll(rc)
	if err != nil {
		if onConflict != nil {
			onConflict()
		}
		return nil, fmt.Errorf("%w: another writer already published L0 %s", ErrConflict, ltx.FormatFilename(minTXID, maxTXID))
	}
	if !bytes.Equal(existing, data) {
		if onConflict != nil {
			onConflict()
		}
		return nil, fmt.Errorf("%w: another writer already published L0 %s", ErrConflict, ltx.FormatFilename(minTXID, maxTXID))
	}
	return &ltx.FileInfo{
		Level:     0,
		MinTXID:   minTXID,
		MaxTXID:   maxTXID,
		Size:      int64(len(data)),
		CreatedAt: ts,
	}, nil
}

// ReadLTXUpload buffers r, parses the LTX header timestamp, and returns the
// bytes to upload. It is used for small level-0 conditional creates.
func ReadLTXUpload(r io.Reader) (data []byte, ts time.Time, err error) {
	data, err = io.ReadAll(r)
	if err != nil {
		return nil, time.Time{}, err
	}
	hdr, _, err := ltx.PeekHeader(bytes.NewReader(data))
	if err != nil {
		return nil, time.Time{}, fmt.Errorf("read LTX header: %w", err)
	}
	return data, time.UnixMilli(hdr.Timestamp).UTC(), nil
}

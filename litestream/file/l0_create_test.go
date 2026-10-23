package file_test

import (
	"bytes"
	"errors"
	"testing"

	"github.com/benbjohnson/litestream"
	"github.com/benbjohnson/litestream/file"
	"github.com/superfly/ltx"
)

func TestReplicaClient_L0CreateOnly(t *testing.T) {
	dir := t.TempDir()
	c := file.NewReplicaClient(dir)
	c.SetL0CreateOnly(true)

	var buf bytes.Buffer
	enc, err := ltx.NewEncoder(&buf)
	if err != nil {
		t.Fatal(err)
	}
	if err := enc.EncodeHeader(ltx.Header{
		Version:   ltx.Version,
		Flags:     ltx.HeaderFlagNoChecksum,
		PageSize:  4096,
		Commit:    1,
		MinTXID:   2,
		MaxTXID:   2,
		Timestamp: 1,
	}); err != nil {
		t.Fatal(err)
	}
	if err := enc.Close(); err != nil {
		t.Fatal(err)
	}
	data := buf.Bytes()

	ctx := t.Context()
	if _, err := c.WriteLTXFile(ctx, 0, 2, 2, bytes.NewReader(data)); err != nil {
		t.Fatalf("first write: %v", err)
	}
	if _, err := c.WriteLTXFile(ctx, 0, 2, 2, bytes.NewReader(data)); err != nil {
		t.Fatalf("idempotent retry: %v", err)
	}
	if c.L0ConflictCount() != 0 {
		t.Fatalf("conflicts = %d, want 0", c.L0ConflictCount())
	}

	other := bytes.Clone(data)
	other[ltx.HeaderSize/2] ^= 0xff
	err = writeErr(c.WriteLTXFile(ctx, 0, 2, 2, bytes.NewReader(other)))
	if !errors.Is(err, litestream.ErrConflict) {
		t.Fatalf("conflicting write error = %v, want ErrConflict", err)
	}
	if c.L0ConflictCount() != 1 {
		t.Fatalf("conflicts = %d, want 1", c.L0ConflictCount())
	}
}

func writeErr[T any](_ T, err error) error { return err }

package store

import (
	"database/sql"
	"fmt"
	"net"
	"sync"
	"testing"

	"github.com/benbjohnson/litestream"
	"github.com/fsouza/fake-gcs-server/fakestorage"
)

// Cloud Storage is what Cloud Run uses. This runs two overlapping instances
// against an in-process fake, so conditional L0 creates go through the
// Cloud Storage client and Litestream's gs client lists what they wrote.
func TestCloudStorageOverlappingInstances(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	port := ln.Addr().(*net.TCPAddr).Port
	ln.Close()
	host := fmt.Sprintf("127.0.0.1:%d", port)
	// The Cloud Storage client reads objects from http://HOST/bucket/object,
	// which the fake serves only when HOST is its public host.
	srv, err := fakestorage.NewServerWithOptions(fakestorage.Options{
		Scheme:     "http",
		Host:       "127.0.0.1",
		Port:       uint16(port),
		PublicHost: host,
	})
	if err != nil {
		t.Fatal(err)
	}
	defer srv.Stop()
	srv.CreateBucketWithOpts(fakestorage.CreateBucketOpts{Name: "replica"})
	t.Setenv("STORAGE_EMULATOR_HOST", host)

	cfg := testConfig(t, "")
	cfg.ReplicaURL = "gs://replica/db"
	a := mustOpen(t, cfg)
	mustWrite(t, a, "CREATE TABLE t (id INTEGER PRIMARY KEY, who TEXT)")
	cfg.Dir = t.TempDir()
	b := mustOpen(t, cfg)

	var wg sync.WaitGroup
	for _, inst := range []struct {
		name string
		s    *Store
	}{{"a", a}, {"b", b}} {
		wg.Go(func() {
			for range 25 {
				if err := inst.s.Write(t.Context(), func(tx *sql.Tx) error {
					_, err := tx.Exec("INSERT INTO t (who) VALUES (?)", inst.name)
					return err
				}); err != nil {
					t.Errorf("%s write: %v", inst.name, err)
				}
			}
		})
	}
	wg.Wait()
	conflicts := litestream.ReplicaL0ConflictCount(a.client.ReplicaClient) + litestream.ReplicaL0ConflictCount(b.client.ReplicaClient)
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	if err := b.Close(); err != nil {
		t.Fatal(err)
	}

	cfg.Dir = t.TempDir()
	c := mustOpen(t, cfg)
	defer c.Close()
	if got := count(t, c, "t"); got != 50 {
		t.Fatalf("rows = %d, want 50", got)
	}
	integrity(t, c)
	t.Logf("%d conditional creates found another instance's transaction", conflicts)
}

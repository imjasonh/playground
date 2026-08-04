package snapshot

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestLocalStoreRoundTrip(t *testing.T) {
	t.Parallel()
	root := t.TempDir()
	store, err := NewLocalStore(filepath.Join(root, "blobs"))
	if err != nil {
		t.Fatal(err)
	}
	src := NewPackageDir(filepath.Join(root, "src"))
	if err := os.MkdirAll(src.Dir, 0o755); err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"vm.state", "vm.mem", "rootfs.ext4"} {
		if err := os.WriteFile(filepath.Join(src.Dir, name), []byte(name+"-data"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	meta := Meta{User: "alice", App: "fortune", GuestIP: "172.16.1.2", TapName: "fc-1", CreatedAt: time.Now().UTC()}
	if err := src.WriteMeta(meta); err != nil {
		t.Fatal(err)
	}
	ctx := context.Background()
	key := KeyFor("alice", "fortune")
	if err := store.Put(ctx, key, src); err != nil {
		t.Fatal(err)
	}
	if !store.Exists(key) {
		t.Fatal("expected exists")
	}
	dstDir := filepath.Join(root, "dst")
	got, err := store.Get(ctx, key, dstDir)
	if err != nil {
		t.Fatal(err)
	}
	if got.Meta.User != "alice" || got.Meta.App != "fortune" {
		t.Fatalf("meta: %+v", got.Meta)
	}
	b, err := os.ReadFile(got.StatePath)
	if err != nil || string(b) != "vm.state-data" {
		t.Fatalf("state: %q %v", b, err)
	}
	if err := store.Delete(ctx, key); err != nil {
		t.Fatal(err)
	}
	if store.Exists(key) {
		t.Fatal("expected deleted")
	}
}

func TestLocalStoreRejectsTraversalKey(t *testing.T) {
	t.Parallel()
	s, err := NewLocalStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	pkg := NewPackageDir(t.TempDir())
	if err := s.Put(context.Background(), "../outside", pkg); err == nil {
		t.Fatal("expected traversal key to be rejected")
	}
	if err := s.Delete(context.Background(), "alice/../../outside"); err == nil {
		t.Fatal("expected traversal key to be rejected")
	}
}

func TestLocalStoreHasRejectsIncompletePackage(t *testing.T) {
	t.Parallel()
	root := t.TempDir()
	store, err := NewLocalStore(root)
	if err != nil {
		t.Fatal(err)
	}
	key := KeyFor("alice", "fortune")
	dir, err := store.keyDir(key)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "meta.json"), []byte("{}"), 0o644); err != nil {
		t.Fatal(err)
	}
	if ok, err := store.Has(context.Background(), key); err != nil || ok {
		t.Fatalf("incomplete package reported present: ok=%v err=%v", ok, err)
	}
}

package blob

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

func TestPutGetHas(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	b := []byte("compiled object file")
	d := digest.FromBytes(b)

	if s.Has(d) {
		t.Fatal("empty store claims to have blob")
	}
	if err := s.Put(d, b); err != nil {
		t.Fatalf("Put: %v", err)
	}
	if !s.Has(d) {
		t.Fatal("store lost blob after Put")
	}
	got, err := s.Get(d)
	if err != nil {
		t.Fatalf("Get: %v", err)
	}
	if string(got) != string(b) {
		t.Errorf("Get = %q, want %q", got, b)
	}
}

func TestPutRejectsMismatch(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	d := digest.FromBytes([]byte("real"))
	if err := s.Put(d, []byte("lies")); err == nil {
		t.Error("Put stored bytes that do not match the digest")
	}
	if s.Has(d) {
		t.Error("rejected Put left a blob behind")
	}
}

func TestRejectsMalformedDigests(t *testing.T) {
	root := t.TempDir()
	secret := filepath.Join(root, "secret")
	if err := os.WriteFile(secret, []byte("not a blob"), 0o600); err != nil {
		t.Fatal(err)
	}
	s, err := NewStore(filepath.Join(root, "store"))
	if err != nil {
		t.Fatal(err)
	}
	for _, d := range []*repb.Digest{
		{Hash: "../../secret", SizeBytes: 10},
		{Hash: "../secret", SizeBytes: 10},
		{Hash: "ab", SizeBytes: 0},
		{Hash: strings.Repeat("A", 64), SizeBytes: 0},
		{Hash: strings.Repeat("a", 64), SizeBytes: -1},
		nil,
	} {
		if _, err := s.Get(d); err == nil || err == ErrNotFound {
			t.Errorf("Get(%v) = %v, want a validation error", d, err)
		}
		if s.Has(d) {
			t.Errorf("Has(%v) = true", d)
		}
		if err := s.Delete(d); err == nil {
			t.Errorf("Delete(%v) succeeded", d)
		}
	}
	if _, err := os.Stat(secret); err != nil {
		t.Errorf("file outside the store was touched: %v", err)
	}
}

func TestHasChecksSize(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	b := []byte("sized")
	d := digest.FromBytes(b)
	if err := s.Put(d, b); err != nil {
		t.Fatal(err)
	}
	if s.Has(&repb.Digest{Hash: d.GetHash(), SizeBytes: d.GetSizeBytes() + 1}) {
		t.Error("Has matched a digest with the wrong size")
	}
}

func TestGetMissing(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := s.Get(digest.FromBytes([]byte("absent"))); err != ErrNotFound {
		t.Errorf("Get of missing blob = %v, want ErrNotFound", err)
	}
}

func TestDelete(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	b := []byte("evict me")
	d := digest.FromBytes(b)
	if err := s.Put(d, b); err != nil {
		t.Fatal(err)
	}
	if err := s.Delete(d); err != nil {
		t.Fatalf("Delete: %v", err)
	}
	if s.Has(d) {
		t.Error("blob survived Delete")
	}
	if err := s.Delete(d); err != nil {
		t.Errorf("Delete of absent blob = %v, want nil", err)
	}
}

func TestPutIsAtomic(t *testing.T) {
	root := t.TempDir()
	s, err := NewStore(root)
	if err != nil {
		t.Fatal(err)
	}
	b := []byte("atomic")
	d := digest.FromBytes(b)
	if err := s.Put(d, b); err != nil {
		t.Fatal(err)
	}
	// No stray temp files should remain anywhere under the root.
	err = filepath.WalkDir(root, func(path string, de os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !de.IsDir() && filepath.Base(path)[0] == '.' {
			t.Errorf("leftover temp file: %s", path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
}

func TestPutReaderAndOpen(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	payload := strings.Repeat("streaming blob data\n", 1000)
	d := digest.FromBytes([]byte(payload))
	if err := s.PutReader(d, strings.NewReader(payload)); err != nil {
		t.Fatalf("PutReader: %v", err)
	}
	f, sz, err := s.Open(d)
	if err != nil {
		t.Fatalf("Open: %v", err)
	}
	defer f.Close()
	if sz != int64(len(payload)) {
		t.Fatalf("size = %d, want %d", sz, len(payload))
	}
	got, err := s.Get(d)
	if err != nil {
		t.Fatalf("Get: %v", err)
	}
	if string(got) != payload {
		t.Errorf("Get content mismatch")
	}

	// Wrong hash and wrong length must be rejected.
	if err := s.PutReader(d, strings.NewReader(payload+"extra")); err == nil {
		t.Error("PutReader accepted oversized stream")
	}
	if err := s.PutReader(d, strings.NewReader("short")); err == nil {
		t.Error("PutReader accepted undersized stream")
	}
	bad := strings.Replace(payload, "s", "S", 1)
	if err := s.PutReader(d, strings.NewReader(bad)); err == nil {
		t.Error("PutReader accepted mismatched hash")
	}
}

func TestLRUEviction(t *testing.T) {
	// Limit to 250 bytes: storing three 100-byte blobs should evict the oldest.
	s, err := NewStoreWithLimit(t.TempDir(), 250)
	if err != nil {
		t.Fatal(err)
	}
	b1 := []byte(strings.Repeat("a", 100))
	b2 := []byte(strings.Repeat("b", 100))
	b3 := []byte(strings.Repeat("c", 100))
	d1, d2, d3 := digest.FromBytes(b1), digest.FromBytes(b2), digest.FromBytes(b3)

	if err := s.Put(d1, b1); err != nil {
		t.Fatal(err)
	}
	// Backdate b1 and b2 so b1 is clearly oldest, then touch b1 via Has so b2 becomes oldest.
	p1, _ := s.path(d1)
	p2, _ := s.path(d2)
	if err := s.Put(d2, b2); err != nil {
		t.Fatal(err)
	}
	t1 := time.Now().Add(-10 * time.Second)
	t2 := time.Now().Add(-5 * time.Second)
	old1 := os.Chtimes(p1, t1, t1)
	old2 := os.Chtimes(p2, t2, t2)
	if old1 != nil || old2 != nil {
		t.Fatalf("Chtimes: %v %v", old1, old2)
	}
	// Access d1 so it becomes more recent than d2.
	if !s.Has(d1) {
		t.Fatal("d1 missing before eviction")
	}
	// Adding d3 pushes usage to 300 > 250, evicting d2 (oldest) to target <= 212.
	if err := s.Put(d3, b3); err != nil {
		t.Fatal(err)
	}
	if s.Has(d2) {
		t.Error("least-recently-used blob d2 was not evicted")
	}
	if !s.Has(d1) {
		t.Error("recently-used blob d1 was evicted")
	}
	if !s.Has(d3) {
		t.Error("newest blob d3 was evicted")
	}
	if s.Evictions() < 1 {
		t.Errorf("Evictions = %d, want >= 1", s.Evictions())
	}
}

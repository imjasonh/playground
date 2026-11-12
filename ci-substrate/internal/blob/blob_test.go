package blob

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

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

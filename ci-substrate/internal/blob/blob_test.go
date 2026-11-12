package blob

import (
	"os"
	"path/filepath"
	"testing"

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

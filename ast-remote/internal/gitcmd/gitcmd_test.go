package gitcmd_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/gitcmd"
)

func TestWriteObjectRoundTrip(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not available")
	}
	dir := t.TempDir()
	must(t, exec.Command("git", "init", "-b", "main", dir).Run())
	repo := gitcmd.New(dir, filepath.Join(dir, ".git"))

	data := []byte("package main\n\nfunc main() {}\n")
	oid, err := repo.WriteObject("blob", data)
	if err != nil {
		t.Fatal(err)
	}
	if len(oid) != 40 {
		t.Fatalf("oid=%q", oid)
	}

	// git should see it
	out, err := exec.Command("git", "-C", dir, "cat-file", "blob", oid).Output()
	if err != nil {
		t.Fatal(err)
	}
	if string(out) != string(data) {
		t.Fatalf("mismatch: %q vs %q", out, data)
	}

	// idempotent
	oid2, err := repo.WriteObjectExpected("blob", data, oid)
	if err != nil {
		t.Fatal(err)
	}
	if oid2 != oid {
		t.Fatalf("%s != %s", oid2, oid)
	}
}

func TestCatFileBatch(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not available")
	}
	dir := t.TempDir()
	must(t, exec.Command("git", "init", "-b", "main", dir).Run())
	repo := gitcmd.New(dir, filepath.Join(dir, ".git"))

	var oids []string
	for i := 0; i < 5; i++ {
		data := []byte{byte('a' + i)}
		oid, err := repo.WriteObject("blob", data)
		if err != nil {
			t.Fatal(err)
		}
		oids = append(oids, oid)
	}
	batch, err := repo.CatFileBatch(oids)
	if err != nil {
		t.Fatal(err)
	}
	if len(batch) != 5 {
		t.Fatalf("len=%d", len(batch))
	}
	for i, b := range batch {
		if b.OID != oids[i] || b.Kind != "blob" || len(b.Data) != 1 {
			t.Fatalf("bad entry %#v", b)
		}
	}
}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

var _ = os.DevNull

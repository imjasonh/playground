package asp1_test

import (
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/asp1"
	"github.com/imjasonh/playground/ast-remote/internal/gitcmd"
)

func TestEncodeInstallRoundTrip(t *testing.T) {
	objs := []asp1.Object{
		{Kind: "blob", Path: "b.txt", OID: "", Data: []byte("hello world\n")},
		{Kind: "blob", Path: "a.go", OID: "", Data: []byte("package main\n\nfunc main() {}\n")},
	}
	dir := t.TempDir()
	if err := exec.Command("git", "init", "--quiet", dir).Run(); err != nil {
		t.Fatal(err)
	}
	repo := gitcmd.New(dir, filepath.Join(dir, ".git"))
	for i := range objs {
		oid, err := repo.WriteObject(objs[i].Kind, objs[i].Data)
		if err != nil {
			t.Fatal(err)
		}
		objs[i].OID = oid
	}

	stream, err := asp1.Encode(objs)
	if err != nil {
		t.Fatal(err)
	}
	if len(stream) < 6 || string(stream[:4]) != asp1.Magic {
		t.Fatalf("bad stream header")
	}

	decoded, err := asp1.Decode(stream)
	if err != nil {
		t.Fatal(err)
	}
	if len(decoded) != len(objs) {
		t.Fatalf("decoded %d want %d", len(decoded), len(objs))
	}
	// Encode sorts by path: a.go before b.txt
	if decoded[0].OID != objs[1].OID || decoded[1].OID != objs[0].OID {
		t.Fatalf("expected path-sorted order, got %s then %s", decoded[0].OID[:8], decoded[1].OID[:8])
	}

	dir2 := t.TempDir()
	if err := exec.Command("git", "init", "--quiet", dir2).Run(); err != nil {
		t.Fatal(err)
	}
	n, err := asp1.Install(filepath.Join(dir2, ".git"), stream)
	if err != nil {
		t.Fatal(err)
	}
	if n != len(objs) {
		t.Fatalf("installed %d want %d", n, len(objs))
	}
	repo2 := gitcmd.New(dir2, filepath.Join(dir2, ".git"))
	for _, o := range objs {
		got, err := repo2.CatFile(o.Kind, o.OID)
		if err != nil {
			t.Fatal(err)
		}
		if string(got) != string(o.Data) {
			t.Fatalf("cat-file mismatch for %s", o.OID)
		}
	}
}

func TestSortForEncode(t *testing.T) {
	objs := []asp1.Object{
		{Kind: "blob", Path: "z", OID: "bb"},
		{Kind: "commit", Path: "", OID: "aa"},
		{Kind: "blob", Path: "a", OID: "cc"},
		{Kind: "tree", Path: "dir", OID: "dd"},
	}
	asp1.SortForEncode(objs)
	want := []string{"aa", "dd", "cc", "bb"}
	for i, o := range objs {
		if o.OID != want[i] {
			t.Fatalf("pos %d: got %s want %s", i, o.OID, want[i])
		}
	}
}

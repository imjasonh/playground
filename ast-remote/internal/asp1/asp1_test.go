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
	if len(stream) < 8 || string(stream[:4]) != asp1.Magic || stream[4] != asp1.Version {
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

func TestV1InstallCompat(t *testing.T) {
	// Build a v1 stream manually via Decode path: encode then rewrite header is hard;
	// instead verify Install accepts a single-frame v1 by using Encode of one object
	// and checking Version is 2, then separately craft v1 with Encode internals.
	objs := []asp1.Object{
		{Kind: "blob", Path: "x", OID: "", Data: []byte("compat\n")},
	}
	dir := t.TempDir()
	if err := exec.Command("git", "init", "--quiet", dir).Run(); err != nil {
		t.Fatal(err)
	}
	repo := gitcmd.New(dir, filepath.Join(dir, ".git"))
	oid, err := repo.WriteObject(objs[0].Kind, objs[0].Data)
	if err != nil {
		t.Fatal(err)
	}
	objs[0].OID = oid

	stream, err := asp1.Encode(objs)
	if err != nil {
		t.Fatal(err)
	}
	// Convert v2 single-frame to v1: ASP1 | 1 | codec | frame_bytes
	if stream[4] != asp1.Version {
		t.Fatalf("want v2")
	}
	nframes := int(stream[6])<<8 | int(stream[7])
	if nframes != 1 {
		t.Fatalf("want 1 frame got %d", nframes)
	}
	clen := int(stream[8])<<24 | int(stream[9])<<16 | int(stream[10])<<8 | int(stream[11])
	frame := stream[12 : 12+clen]
	v1 := append([]byte(asp1.Magic), asp1.VersionV1, asp1.CodecZstd)
	v1 = append(v1, frame...)

	dir2 := t.TempDir()
	if err := exec.Command("git", "init", "--quiet", dir2).Run(); err != nil {
		t.Fatal(err)
	}
	n, err := asp1.Install(filepath.Join(dir2, ".git"), v1)
	if err != nil {
		t.Fatal(err)
	}
	if n != 1 {
		t.Fatalf("installed %d", n)
	}
}

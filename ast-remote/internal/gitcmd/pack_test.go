package gitcmd_test

import (
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/gitcmd"
)

func TestBuildPackAndIndexPack(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not available")
	}
	dir := t.TempDir()
	must(t, exec.Command("git", "init", "-b", "main", dir).Run())
	repo := gitcmd.New(dir, filepath.Join(dir, ".git"))

	blobs := [][]byte{
		[]byte("one\n"),
		[]byte("two\n"),
		[]byte("three\n"),
	}
	// Compute OIDs via WriteObject in a scratch repo, then install via pack
	// into a fresh repo.
	var objs []gitcmd.PackObject
	var oids []string
	for _, b := range blobs {
		oid, err := repo.WriteObject("blob", b)
		if err != nil {
			t.Fatal(err)
		}
		oids = append(oids, oid)
		objs = append(objs, gitcmd.PackObject{Kind: "blob", Data: b})
	}

	dir2 := t.TempDir()
	must(t, exec.Command("git", "init", "-b", "main", dir2).Run())
	repo2 := gitcmd.New(dir2, filepath.Join(dir2, ".git"))

	pack, err := gitcmd.BuildPack(objs)
	if err != nil {
		t.Fatal(err)
	}
	if err := repo2.IndexPack(pack); err != nil {
		t.Fatal(err)
	}
	for i, oid := range oids {
		out, err := exec.Command("git", "-C", dir2, "cat-file", "blob", oid).Output()
		if err != nil {
			t.Fatalf("missing %s: %v", oid, err)
		}
		if string(out) != string(blobs[i]) {
			t.Fatalf("content mismatch for %s", oid)
		}
	}
}

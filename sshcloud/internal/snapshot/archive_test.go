package snapshot

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"
)

func TestCanonicalArchiveRoundTripRejectsTrailingBytes(t *testing.T) {
	t.Parallel()
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	pkg := testPackage(t, ref)
	var archive bytes.Buffer
	if err := WriteArchive(
		t.Context(),
		&archive,
		ref,
		pkg,
		"firecracker-jailer-v1",
	); err != nil {
		t.Fatal(err)
	}
	if _, err := ReadArchive(
		t.Context(),
		bytes.NewReader(archive.Bytes()),
		ref,
		filepath.Join(t.TempDir(), "valid"),
		"firecracker-jailer-v1",
	); err != nil {
		t.Fatalf("read canonical archive: %v", err)
	}

	withTrailing := append(append([]byte(nil), archive.Bytes()...), 1)
	if _, err := ReadArchive(
		t.Context(),
		bytes.NewReader(withTrailing),
		ref,
		filepath.Join(t.TempDir(), "trailing"),
		"firecracker-jailer-v1",
	); err == nil {
		t.Fatal("archive with trailing bytes was accepted")
	}
}

func TestValidatePackageRejectsExtraEntriesAndNonCanonicalPaths(t *testing.T) {
	t.Parallel()
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}

	t.Run("extra entry", func(t *testing.T) {
		pkg := testPackage(t, ref)
		if err := os.WriteFile(filepath.Join(pkg.Dir, "extra"), []byte("extra"), 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := ValidatePackage(ref, pkg, "firecracker-jailer-v1"); err == nil {
			t.Fatal("package with extra entry was accepted")
		}
	})

	t.Run("caller supplied path", func(t *testing.T) {
		pkg := testPackage(t, ref)
		pkg.StatePath = filepath.Join(pkg.Dir, "vm.mem")
		if _, err := ValidatePackage(ref, pkg, "firecracker-jailer-v1"); err == nil {
			t.Fatal("package with noncanonical paths was accepted")
		}
	})
}

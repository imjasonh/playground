//go:build vfs

package litestream

import (
	"slices"
	"testing"
	"time"
)

func TestVFSFile_PageReadHook(t *testing.T) {
	type read struct {
		source PageReadSource
		d      time.Duration
	}
	var got []read
	hook := func(source PageReadSource, d time.Duration) {
		got = append(got, read{source, d})
	}
	readPage := func(t *testing.T, f *VFSFile, pgno uint32) {
		t.Helper()
		buf := make([]byte, ilPageSize)
		if _, err := f.ReadAt(buf, int64(pgno-1)*ilPageSize); err != nil {
			t.Fatalf("read page %d: %v", pgno, err)
		}
	}
	sources := func() []PageReadSource {
		var s []PageReadSource
		for _, r := range got {
			if r.d < 0 {
				t.Errorf("%s read took %v", r.source, r.d)
			}
			s = append(s, r.source)
		}
		got = nil
		return s
	}

	client := newMemClient()
	w, err := openTestFile(t.TempDir(), client, true)
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()
	w.pageReadHook = hook

	// A new database's pages aren't in the page index yet. The writer reads
	// them as zeros, which isn't a page read.
	for pgno := uint32(1); pgno <= 3; pgno++ {
		readPage(t, w, pgno)
	}
	if s := sources(); len(s) != 0 {
		t.Fatalf("reads of a new database = %v, want none", s)
	}
	for pgno := uint32(1); pgno <= 3; pgno++ {
		if err := commitPage(w, pgno, 1); err != nil {
			t.Fatal(err)
		}
	}
	_ = sources()

	r, err := openTestFile(t.TempDir(), client, false)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	r.pageReadHook = hook
	readPage(t, r, 2)
	readPage(t, r, 2)
	if s, want := sources(), []PageReadSource{PageReadReplica, PageReadCache}; !slices.Equal(s, want) {
		t.Fatalf("reader's reads = %v, want %v", s, want)
	}

	// The writer's upload stays in its overlay until a poll installs it.
	if err := commitPage(w, 2, 2); err != nil {
		t.Fatal(err)
	}
	_ = sources()
	readPage(t, w, 2)
	if s, want := sources(), []PageReadSource{PageReadOverlay}; !slices.Equal(s, want) {
		t.Fatalf("writer's read = %v, want %v", s, want)
	}
}

package store_test

import (
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/codec"
	"github.com/imjasonh/playground/ast-remote/internal/store"
)

func TestPutGet(t *testing.T) {
	root := t.TempDir()
	st, err := store.Open(root)
	if err != nil {
		t.Fatal(err)
	}
	src := []byte("package p\n")
	res, err := codec.EncodeFile("p.go", src)
	if err != nil {
		t.Fatal(err)
	}
	oid := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	err = st.Put(store.Meta{
		OID:      oid,
		Kind:     store.KindBlob,
		Encoding: res.Encoding,
		Size:     res.RawSize,
		Lang:     res.Lang,
	}, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !st.Has(oid) {
		t.Fatal("expected has")
	}
	m, payload, err := st.Get(oid)
	if err != nil {
		t.Fatal(err)
	}
	if m.Encoding != res.Encoding {
		t.Fatalf("encoding %s", m.Encoding)
	}
	back, err := codec.Decode(m.Encoding, payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatal("mismatch")
	}
	if err := st.UpdateRef("refs/heads/main", oid); err != nil {
		t.Fatal(err)
	}
	refs, err := st.ListRefs()
	if err != nil {
		t.Fatal(err)
	}
	if refs["refs/heads/main"] != oid {
		t.Fatalf("refs=%v", refs)
	}
}

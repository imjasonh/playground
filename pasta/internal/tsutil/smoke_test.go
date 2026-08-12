package tsutil

import (
	"testing"

	"github.com/imjasonh/pasta/internal/tswasm"
)

func TestSmokeParseGo(t *testing.T) {
	src := []byte(`package p

func f() error {
	err := foo()
	if err != nil {
		return err
	}
	return nil
}
`)

	tree, root, err := Parse(t.Context(), &tswasm.Language{Grammar: "go"}, src, "")
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	defer tree.Release()

	if root.Type() != "source_file" {
		t.Fatalf("root type = %q, want source_file", root.Type())
	}
	if root.HasError() {
		t.Fatalf("parse produced error nodes: %s", root.String())
	}
}

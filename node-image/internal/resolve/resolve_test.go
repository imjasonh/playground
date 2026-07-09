package resolve_test

import (
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestClosurePureJS(t *testing.T) {
	path := filepath.Join("..", "..", "testdata", "pure-js", "pnpm-lock.yaml")
	l, err := lock.ParseFile(path)
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 1 {
		t.Fatalf("got %d refs: %+v", len(refs), refs)
	}
	if refs[0].Name != "ms" || refs[0].Version != "2.1.3" {
		t.Fatalf("ref: %+v", refs[0])
	}
	if refs[0].Integrity == "" || refs[0].Tarball == "" {
		t.Fatalf("missing fetch info: %+v", refs[0])
	}
	refs2, err := resolve.Closure(l, ".", resolve.LinuxArm64)
	if err != nil {
		t.Fatal(err)
	}
	if refs2[0].Integrity != refs[0].Integrity {
		t.Fatal("pure-js integrity should be shared across arches")
	}
}

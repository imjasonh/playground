package resolve_test

import (
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestClosureWorkspaceLocal(t *testing.T) {
	root := filepath.Join("..", "..", "testdata", "workspace-app")
	l, err := lock.ParseFile(filepath.Join(root, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.ClosureOpts(l, "apps/api", resolve.LinuxAmd64, resolve.ClosureOptions{LockRoot: root})
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 1 {
		t.Fatalf("refs=%d %+v", len(refs), refs)
	}
	if !refs[0].IsLocal {
		t.Fatal("expected local package")
	}
	if refs[0].Name != "@fixture/lib" {
		t.Fatalf("name %q", refs[0].Name)
	}
}

func TestClosureCatalogExpanded(t *testing.T) {
	root := filepath.Join("..", "..", "testdata", "catalog-app")
	l, err := lock.ParseFile(filepath.Join(root, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 1 || refs[0].Name != "ms" {
		t.Fatalf("%+v", refs)
	}
}

func TestClosurePatchedSetsPatchPath(t *testing.T) {
	root := filepath.Join("..", "..", "testdata", "patched")
	l, err := lock.ParseFile(filepath.Join(root, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 1 {
		t.Fatalf("%+v", refs)
	}
	if refs[0].PatchPath == "" || refs[0].PatchHash == "" {
		t.Fatalf("expected patch metadata: %+v", refs[0])
	}
}

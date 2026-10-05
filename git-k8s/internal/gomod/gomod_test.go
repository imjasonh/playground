package gomod_test

import (
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/gomod"
)

func TestIsModFile(t *testing.T) {
	for p, want := range map[string]bool{
		"go.mod":                      true,
		"tools/go.mod":                true,
		"_tools/go.mod":               true,
		"go.sum":                      false,
		"x/go.mod.bak":                false,
		"testdata/go.mod":             false,
		"pkg/testdata/m/go.mod":       false,
		"vendor/example.com/m/go.mod": false,
	} {
		if got := gomod.IsModFile(p); got != want {
			t.Errorf("IsModFile(%q) = %t, want %t", p, got, want)
		}
	}
}

func TestFiles(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("go.mod", "module example.com/app\n")
	w.Write("tools/go.mod", "module example.com/app/tools\n")
	w.Write("testdata/go.mod", "module example.com/fake\n")
	if err := os.MkdirAll(filepath.Join(w.Dir, "link"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink("../go.mod", filepath.Join(w.Dir, "link", "go.mod")); err != nil {
		t.Fatal(err)
	}
	head := w.Commit("modules")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	files, err := gomod.Files(ctx, repo, head)
	if err != nil {
		t.Fatal(err)
	}
	var paths []string
	for _, f := range files {
		paths = append(paths, f.Path)
	}
	if want := []string{"go.mod", "tools/go.mod"}; !slices.Equal(paths, want) {
		t.Errorf("Files = %v, want %v", paths, want)
	}
}

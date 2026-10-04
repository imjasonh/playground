package gocache

import (
	"archive/zip"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

func TestAsmStrings(t *testing.T) {
	for _, tc := range []struct {
		src  string
		want []string
		ok   bool
	}{
		{"#include \"textflag.h\"\n#include \"../inc/val.h\"\n", []string{"textflag.h", "../inc/val.h"}, true},
		{"// #include \"commented.h\"\n/* #include \"block.h\" */\nTEXT ·f(SB),0,$0\n", nil, true},
		{"#include \"\\x2e\\x2e/escaped.h\"\n", []string{"../escaped.h"}, true},
		{"#define S \"a\" // 'b'\nMOVB $'c', AX\n", []string{"a"}, true},
		{"#include \"unterminated\n", nil, false},
	} {
		got, ok := asmStrings([]byte(tc.src))
		if !slices.Equal(got, tc.want) || ok != tc.ok {
			t.Errorf("asmStrings(%q) = %q, %t; want %q, %t", tc.src, got, ok, tc.want, tc.ok)
		}
	}
}

func TestShareable(t *testing.T) {
	root := t.TempDir()
	goroot, modcache, repo := filepath.Join(root, "goroot"), filepath.Join(root, "mod"), filepath.Join(root, "src", "repo")
	dep := filepath.Join(modcache, "example.com", "dep@v1.0.0")
	files := map[string]string{
		"goroot/src/runtime/asm_amd64.s":                 "#include \"go_asm.h\"\n#include \"textflag.h\"\n#include \"asm_amd64.h\"\n",
		"goroot/src/runtime/asm_amd64.h":                 "#include \"funcdata.h\"\n",
		"mod/example.com/dep@v1.0.0/escapes/x_amd64.s":   "#include \"../inc/val.h\"\n",
		"mod/example.com/dep@v1.0.0/abs/x_amd64.s":       "#include \"/src/repo/inc/val.h\"\n",
		"mod/example.com/dep@v1.0.0/nested/x_amd64.s":    "#include \"local.h\"\n",
		"mod/example.com/dep@v1.0.0/nested/local.h":      "#include \"../inc/val.h\"\n",
		"mod/example.com/dep@v1.0.0/linked/x_amd64.s":    "#include \"link.h\"\n",
		"mod/example.com/dep@v1.0.0/broken/x_amd64.s":    "#include \"unterminated\n",
		"mod/example.com/dep@v1.0.0/inc/val.h":           "#define VAL $41\n",
		"mod/cache/download/example.com/odd/x/x_amd64.s": "TEXT ·f(SB),0,$0\n",
	}
	for name, src := range files {
		path := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.Symlink(filepath.Join(repo, "inc", "val.h"), filepath.Join(dep, "linked", "link.h")); err != nil {
		t.Fatal(err)
	}
	pkgs := []listedPackage{
		{ImportPath: "unsafe", Dir: filepath.Join(goroot, "src", "unsafe")},
		{ImportPath: "runtime", Dir: filepath.Join(goroot, "src", "runtime"), SFiles: []string{"asm_amd64.s"}, Deps: []string{"unsafe"}},
		{ImportPath: "fmt", Dir: filepath.Join(goroot, "src", "fmt") + "/", Deps: []string{"runtime", "unsafe"}},
		{ImportPath: "example.com/dep", Dir: dep, Deps: []string{"fmt", "runtime", "unsafe"}},
		{ImportPath: "example.com/dep/escapes", Dir: filepath.Join(dep, "escapes"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/abs", Dir: filepath.Join(dep, "abs"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/nested", Dir: filepath.Join(dep, "nested"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/linked", Dir: filepath.Join(dep, "linked"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/broken", Dir: filepath.Join(dep, "broken"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/missing", Dir: filepath.Join(dep, "missing"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep/user", Dir: filepath.Join(dep, "user"), Deps: []string{"example.com/dep/escapes", "fmt"}},
		{ImportPath: "example.com/dep/unlisted", Dir: filepath.Join(dep, "unlisted"), Deps: []string{"example.com/absent"}},
		{ImportPath: "example.com/odd/x", Dir: filepath.Join(modcache, "cache", "download", "example.com", "odd", "x"), SFiles: []string{"x_amd64.s"}},
		{ImportPath: "example.com/dep [example.com/m.test]", Dir: dep, ForTest: "example.com/m", Deps: []string{"fmt"}},
		{ImportPath: "example.com/m", Dir: repo, Deps: []string{"fmt"}},
		{ImportPath: "example.com/v", Dir: filepath.Join(repo, "vendor", "example.com", "v")},
		{ImportPath: "example.com/replaced", Dir: filepath.Join(root, "src", "replaced")},
		{ImportPath: "example.com/sibling", Dir: filepath.Join(root, "goroot2", "src", "x")},
		{ImportPath: "example.com/climbs", Dir: goroot + "/../src/repo/x"},
		{ImportPath: "example.com/relative", Dir: filepath.Join("goroot", "src", "x")},
		{ImportPath: "example.com/error"},
	}
	want := []string{"unsafe", "runtime", "fmt", "example.com/dep"}
	if got := shareable(pkgs, goroot, modcache); !slices.Equal(got, want) {
		t.Errorf("shareable = %q, want %q", got, want)
	}
}

// addModule adds a module to the file-based module proxy in dir.
func addModule(t *testing.T, dir, path, version string, files map[string]string) {
	t.Helper()
	v := filepath.Join(dir, path, "@v")
	if err := os.MkdirAll(v, 0o755); err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	zw := zip.NewWriter(&buf)
	for name, src := range files {
		w, err := zw.Create(path + "@" + version + "/" + name)
		if err != nil {
			t.Fatal(err)
		}
		w.Write([]byte(src))
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	for ext, content := range map[string][]byte{
		".info": []byte(`{"Version":"` + version + `"}`),
		".mod":  []byte(files["go.mod"]),
		".zip":  buf.Bytes(),
	} {
		if err := os.WriteFile(filepath.Join(v, version+ext), content, 0o644); err != nil {
			t.Fatal(err)
		}
	}
}

// TestBuild runs Build for a module that depends on a module from a module
// proxy, with this binary as the GOCACHEPROG program, and then again with
// an empty local directory.
func TestBuild(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("go isn't installed")
	}
	self, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	proxy, mod, home := t.TempDir(), t.TempDir(), t.TempDir()
	addModule(t, proxy, "example.com/dep", "v1.0.0", map[string]string{
		"go.mod": "module example.com/dep\n\ngo 1.24\n",
		"dep.go": "package dep\n\nimport \"strings\"\n\nfunc Up(s string) string { return strings.ToUpper(s) }\n",
	})
	for name, src := range map[string]string{
		"go.mod":      "module example.com/m\n\ngo 1.24\n\nrequire example.com/dep v1.0.0\n",
		"a/a.go":      "package a\n\nimport \"example.com/dep\"\n\nfunc A() string { return dep.Up(\"a\") }\n",
		"a/a_test.go": "package a\n\nimport \"testing\"\n\nfunc TestA(t *testing.T) {\n\tif A() != \"A\" {\n\t\tt.Fail()\n\t}\n}\n",
	} {
		if err := os.MkdirAll(filepath.Join(mod, filepath.Dir(name)), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(mod, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	r, srv, tokenFile := newRemote(t)
	remoteURL := srv.URL + Path("ns", "app")
	t.Chdir(mod)
	for k, v := range map[string]string{
		"HOME": home, "GOENV": "off", "GOFLAGS": "-modcacherw -mod=mod", "GOPATH": filepath.Join(home, "go"),
		"GOCACHE": filepath.Join(home, "go-build"), "GOTOOLCHAIN": "local", "GOPROXY": "file://" + filepath.ToSlash(proxy),
		"GOSUMDB": "off", "CGO_ENABLED": "0", "GOCACHEPROG": "",
		"GOCACHE_TEST_REMOTE": remoteURL, "GOCACHE_TEST_TOKEN": tokenFile, "GOCACHE_TEST_SHARE": "1",
	} {
		t.Setenv(k, v)
	}
	build := func(dir string) (shared []string, total int) {
		t.Helper()
		t.Setenv("GOCACHE_TEST_DIR", dir)
		var stderr bytes.Buffer
		shared, total, err := Build(t.Context(), self, &stderr)
		if err != nil {
			t.Fatalf("Build: %v\n%s", err, stderr.Bytes())
		}
		return shared, total
	}

	first := t.TempDir()
	shared, total := build(first)
	if !slices.Contains(shared, "strings") || !slices.Contains(shared, "example.com/dep") || total <= len(shared) {
		t.Errorf("Build shared %q of %d packages; want strings and example.com/dep, and not every package", shared, total)
	}
	if slices.ContainsFunc(shared, func(p string) bool { return strings.HasPrefix(p, "example.com/m") }) {
		t.Errorf("Build shared %q, which includes the module's own packages", shared)
	}
	stored, had, err := Upload(t.Context(), nil, first, remoteURL, tokenFile)
	if err != nil || stored == 0 || had != 0 {
		t.Fatalf("Upload = %d stored, %d had, %v", stored, had, err)
	}

	t.Log("The module's own packages compile without the build cache, as in the test container, so none of their outputs reach go-cache.")
	cmd := exec.Command("go", "list", "-export", "-f={{.Export}}", "./...")
	cmd.Env = append(os.Environ(), "GOCACHEPROG="+self, "GOCACHE_TEST_DIR="+first, "GOCACHE_TEST_REMOTE=", "GOCACHE_TEST_SHARE=")
	out, err := cmd.Output()
	if err != nil {
		t.Fatalf("go list: %v", err)
	}
	r.mu.Lock()
	for _, export := range strings.Fields(string(out)) {
		for action, body := range r.outputs {
			if sum := sha256.Sum256(body); hex.EncodeToString(sum[:]) == filepath.Base(export) {
				t.Errorf("go-cache has %s, the export data of a package in the module, for action %s", export, action)
			}
		}
	}
	r.mu.Unlock()

	second := t.TempDir()
	if again, _ := build(second); !slices.Equal(again, shared) {
		t.Errorf("the second Build shared %q, want %q", again, shared)
	}
	built, err := os.ReadDir(filepath.Join(second, "p"))
	if hits, _, _ := r.stats(); err != nil || len(built) != 0 || hits == 0 {
		t.Errorf("the second Build compiled %d outputs (%v) and read %d from go-cache; want 0 compiled", len(built), err, hits)
	}
}

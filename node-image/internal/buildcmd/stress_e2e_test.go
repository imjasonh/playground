package buildcmd_test

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/lock"
)

func fixtureDir(t *testing.T, name string) string {
	t.Helper()
	dir, err := filepath.Abs(filepath.Join("..", "..", "testdata", name))
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

func buildNoPush(t *testing.T, dir string, platforms []string) (ref string, stdout, stderr string) {
	t.Helper()
	if platforms == nil {
		platforms = []string{"linux/amd64"}
	}
	out := t.TempDir()
	var outBuf, errBuf bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    out,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: platforms,
		Stdout:    &outBuf,
		Stderr:    &errBuf,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, errBuf.String())
	}
	return ref, outBuf.String(), errBuf.String()
}

func TestE2ENestedDeps(t *testing.T) {
	ref, stdout, _ := buildNoPush(t, fixtureDir(t, "nested-deps"), nil)
	if strings.TrimSpace(stdout) != ref || !strings.HasPrefix(ref, "sha256:") {
		t.Fatalf("stdout contract: %q vs %q", stdout, ref)
	}
}

func TestE2EScopedDep(t *testing.T) {
	ref, stdout, _ := buildNoPush(t, fixtureDir(t, "scoped-dep"), nil)
	if strings.TrimSpace(stdout) != ref {
		t.Fatalf("stdout %q != %q", stdout, ref)
	}
}

func TestE2EWithBin(t *testing.T) {
	_, _, _ = buildNoPush(t, fixtureDir(t, "with-bin"), nil)
}

func TestE2EOptionalPlatformMultiArch(t *testing.T) {
	ref, _, _ := buildNoPush(t, fixtureDir(t, "optional-platform"), []string{"linux/amd64", "linux/arm64"})
	if ref == "" {
		t.Fatal("empty ref")
	}
}

func TestE2ELifecycleNoopScriptsAllowed(t *testing.T) {
	// es5-ext has a no-op postinstall; it must still build (we never run the script).
	_, _, _ = buildNoPush(t, fixtureDir(t, "lifecycle-scripts"), nil)
}

func TestE2EPatchedRejected(t *testing.T) {
	dir := fixtureDir(t, "patched")
	_, err := lock.ParseFile(filepath.Join(dir, "pnpm-lock.yaml"))
	if err == nil {
		t.Fatal("expected patchedDependencies to be rejected")
	}
	if !strings.Contains(err.Error(), "patchedDependencies") {
		t.Fatalf("want patchedDependencies error, got: %v", err)
	}
	var stdout, stderr bytes.Buffer
	_, err = buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err == nil {
		t.Fatal("expected build to fail on patched lock")
	}
	if !strings.Contains(err.Error(), "patchedDependencies") {
		t.Fatalf("want patchedDependencies error, got: %v", err)
	}
}

func TestE2EWorkspaceRejected(t *testing.T) {
	dir := fixtureDir(t, "workspace-app/apps/api")
	var stdout, stderr bytes.Buffer
	_, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err == nil {
		t.Fatal("expected workspace dependency to fail")
	}
	msg := err.Error()
	if !strings.Contains(msg, "workspace") && !strings.Contains(msg, "link:") && !strings.Contains(msg, "directory") {
		t.Fatalf("want workspace/link rejection, got: %v", err)
	}
}

func TestVirtualStoreDirEncoding(t *testing.T) {
	cases := map[string]string{
		"ms@2.1.3": "ms@2.1.3",
		"@sindresorhus/is@4.6.0": "@sindresorhus+is@4.6.0",
		"eslint-config-prettier@9.1.0(eslint@8.57.0)": "eslint-config-prettier@9.1.0_eslint@8.57.0",
	}
	for in, want := range cases {
		if got := layout.VirtualStoreDir(in); got != want {
			t.Fatalf("%q: got %q want %q", in, got, want)
		}
	}
}

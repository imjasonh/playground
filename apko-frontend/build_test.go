package main

import (
	"archive/tar"
	"compress/gzip"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	"chainguard.dev/apko/pkg/build/types"
	"chainguard.dev/apko/pkg/lock"
)

func testPackages() []testPackage {
	return []testPackage{{
		name: "base", version: "1.0-r0", origin: "base", buildDate: testBuildDate,
		files: map[string]string{"etc/": "", "etc/os-release": "ID=test\n", "etc/passwd": "root:x:0:0:root:/root:/bin/sh\n", "etc/group": "root:x:0:\n"},
	}, {
		name: "libfoo", version: "2.0-r1", origin: "foo", buildDate: testBuildDate,
		files: map[string]string{"usr/": "", "usr/lib/": "", "usr/lib/libfoo.so.2": strings.Repeat("f", 4000)},
	}, {
		name: "foo", version: "2.0-r1", origin: "foo", depends: []string{"libfoo"}, buildDate: testBuildDate + 100,
		files: map[string]string{"usr/": "", "usr/bin/": "", "usr/bin/foo": strings.Repeat("F", 3000)},
	}, {
		// The conflict makes apko's resolver report "baz" as a package
		// that must not be installed, which isn't an error.
		name: "bar", version: "0.1-r0", origin: "bar", depends: []string{"!baz"}, buildDate: testBuildDate,
		files: map[string]string{"usr/": "", "usr/bin/": "", "usr/bin/bar": strings.Repeat("b", 2000)},
	}}
}

func testConfig() types.ImageConfiguration {
	uid, gid := uint32(65532), uint32(65532)
	return types.ImageConfiguration{
		Contents: types.ImageContents{
			Repositories: []string{testRepo},
			Keyring:      []string{testRepo + "/" + testKeyName},
			Packages:     []string{"base", "foo", "bar"},
		},
		Accounts: types.ImageAccounts{
			RunAs:  "nonroot",
			Users:  []types.User{{UserName: "nonroot", UID: 65532, GID: &gid}},
			Groups: []types.Group{{GroupName: "nonroot", GID: 65532}},
		},
		Paths: []types.PathMutation{{Path: "/data", Type: "directory", UID: &uid, GID: &gid, Permissions: 0o750}},
	}
}

// fetchDir writes the files that the frontend gives the helper: what the
// repository served while resolving, except indexes, and the packages.
func fetchDir(t *testing.T, repo *testRepository, pkgs []lock.LockPkg) string {
	t.Helper()
	dir := t.TempDir()
	urls := slices.Clone(repo.requested)
	for _, p := range pkgs {
		urls = append(urls, p.URL)
	}
	for _, u := range urls {
		if strings.HasSuffix(u, "/APKINDEX.tar.gz") {
			continue
		}
		data, ok := repo.files[u]
		if !ok {
			continue
		}
		key, err := fetchKey(u)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, key), data, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

type tarEntry struct {
	hdr  *tar.Header
	data string
}

func readLayer(t *testing.T, path string) map[string]tarEntry {
	t.Helper()
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	var r io.Reader = f
	if strings.HasSuffix(path, ".gz") {
		zr, err := gzip.NewReader(f)
		if err != nil {
			t.Fatal(err)
		}
		r = zr
	}
	out := map[string]tarEntry{}
	tr := tar.NewReader(r)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			return out
		} else if err != nil {
			t.Fatal(err)
		}
		data, err := io.ReadAll(tr)
		if err != nil {
			t.Fatal(err)
		}
		out[strings.TrimSuffix(hdr.Name, "/")] = tarEntry{hdr: hdr, data: string(data)}
	}
}

func TestResolveAndBuildLayers(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("x86_64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	ic := testConfig()
	ic.Layering = &types.Layering{Strategy: "origin", Budget: 2}

	locked, err := resolve(ctx, ic, []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	lk := locked[amd64]
	if lk == nil {
		t.Fatalf("resolve returned no configuration for %s: %v", amd64, locked)
	}
	wantPinned := []string{"bar=0.1-r0", "base=1.0-r0", "foo=2.0-r1", "libfoo=2.0-r1"}
	if got := lk.ic.Contents.Packages; !slices.Equal(got, wantPinned) {
		t.Errorf("pinned packages = %v, want %v", got, wantPinned)
	}
	var urls []string
	for _, p := range lk.pkgs {
		urls = append(urls, p.URL)
	}
	slices.Sort(urls)
	wantURLs := []string{
		testRepo + "/x86_64/bar-0.1-r0.apk",
		testRepo + "/x86_64/base-1.0-r0.apk",
		testRepo + "/x86_64/foo-2.0-r1.apk",
		testRepo + "/x86_64/libfoo-2.0-r1.apk",
	}
	if !slices.Equal(urls, wantURLs) {
		t.Errorf("package URLs = %v, want %v", urls, wantURLs)
	}

	out := t.TempDir()
	p, err := buildLayers(ctx, lk.ic, amd64, writeLock(t, lk.lockData), fetchDir(t, repo, lk.pkgs), out)
	if err != nil {
		t.Fatalf("buildLayers: %v", err)
	}
	if want := time.Unix(testBuildDate+100, 0).UTC(); !p.Created.Equal(want) {
		t.Errorf("created = %v, want the newest package build time %v", p.Created, want)
	}

	// Budget 2 gives the largest origin group, foo, its own layer and
	// merges the others, followed by the top layer.
	var groups [][]string
	for _, l := range p.Layers {
		groups = append(groups, l.Packages)
	}
	wantGroups := [][]string{{"foo", "libfoo"}, {"bar", "base"}, nil}
	if !slices.EqualFunc(groups, wantGroups, slices.Equal[[]string]) {
		t.Fatalf("layer packages = %v, want %v", groups, wantGroups)
	}

	fooLayer := readLayer(t, filepath.Join(out, p.Layers[0].File))
	for _, f := range []string{"usr/bin/foo", "usr/lib/libfoo.so.2"} {
		if _, ok := fooLayer[f]; !ok {
			t.Errorf("layer 0 is missing %s", f)
		}
	}
	if _, ok := fooLayer["usr/bin/bar"]; ok {
		t.Error("layer 0 has usr/bin/bar, which belongs in layer 1")
	}
	if idb := fooLayer["usr/lib/apk/db/installed"].data; !strings.Contains(idb, "P:foo\n") || strings.Contains(idb, "P:bar\n") {
		t.Errorf("layer 0's partial installed database should list only foo and libfoo:\n%s", idb)
	}

	// The base package owns /etc/passwd, so its layer has the file with
	// the accounts apko added.
	baseLayer := readLayer(t, filepath.Join(out, p.Layers[1].File))
	if got := baseLayer["etc/passwd"].data; !strings.Contains(got, "nonroot:x:65532:65532:") || !strings.HasPrefix(got, "root:x:0:0:") {
		t.Errorf("/etc/passwd = %q, want root from the base package and nonroot from accounts", got)
	}

	top := readLayer(t, filepath.Join(out, p.Layers[2].File))
	data, ok := top["data"]
	if !ok || data.hdr.Typeflag != tar.TypeDir || data.hdr.Mode&0o777 != 0o750 || data.hdr.Uid != 65532 {
		t.Errorf("/data = %+v, want a directory owned by 65532 with mode 0750", data.hdr)
	}
	if got, want := top["etc/apk/world"].data, strings.Join(wantPinned, "\n")+"\n"; got != want {
		t.Errorf("/etc/apk/world = %q, want %q", got, want)
	}
	if got := top["etc/apk/repositories"].data; got != testRepo+"\n" {
		t.Errorf("/etc/apk/repositories = %q, want %q", got, testRepo+"\n")
	}
	if _, ok := top["etc/apk/keys/"+testKeyName]; !ok {
		t.Errorf("the top layer is missing /etc/apk/keys/%s", testKeyName)
	}
	idb := top["usr/lib/apk/db/installed"].data
	for _, name := range []string{"base", "libfoo", "foo", "bar"} {
		if !strings.Contains(idb, "P:"+name+"\n") {
			t.Errorf("installed database is missing %s:\n%s", name, idb)
		}
	}
}

func TestBuildLayersFromLock(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("amd64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	ic := testConfig()
	ic.Contents.Packages = []string{"bar"}

	locked, err := resolve(ctx, ic, []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	l := lock.Lock{Version: "v1", Contents: lock.LockContents{Packages: locked[amd64].pkgs}}
	data, err := json.Marshal(l)
	if err != nil {
		t.Fatal(err)
	}

	// Record only what installing from the lock fetches.
	repo.requested = nil
	got, err := fromLock(ctx, ic, []types.Architecture{amd64}, l, data, repo)
	if err != nil {
		t.Fatalf("fromLock: %v", err)
	}
	lk := got[amd64]
	if want := []string{"bar=0.1-r0"}; !slices.Equal(lk.ic.Contents.Packages, want) {
		t.Errorf("pinned packages = %v, want %v", lk.ic.Contents.Packages, want)
	}
	out := t.TempDir()
	p, err := buildLayers(ctx, lk.ic, amd64, writeLock(t, lk.lockData), fetchDir(t, repo, lk.pkgs), out)
	if err != nil {
		t.Fatalf("buildLayers: %v", err)
	}
	if len(p.Layers) != 1 {
		t.Fatalf("got %d layers, want 1 without a layering strategy", len(p.Layers))
	}
	layer := readLayer(t, filepath.Join(out, p.Layers[0].File))
	if _, ok := layer["usr/bin/bar"]; !ok {
		t.Error("the layer is missing usr/bin/bar")
	}
	if _, ok := layer["usr/bin/foo"]; ok {
		t.Error("the layer has usr/bin/foo, which the lock doesn't name")
	}
}

func TestBuildLayersMissingPackage(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("amd64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	ic := testConfig()
	locked, err := resolve(ctx, ic, []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	// Leave the packages out of the fetch directory.
	dir := fetchDir(t, repo, nil)
	if _, err := buildLayers(ctx, locked[amd64].ic, amd64, writeLock(t, locked[amd64].lockData), dir, t.TempDir()); err == nil {
		t.Fatal("buildLayers succeeded without the package files")
	}
}

func TestResolveMissingPackage(t *testing.T) {
	repo := newTestRepository(t, "x86_64", testPackages()...)
	ic := testConfig()
	ic.Contents.Packages = []string{"nope"}
	if _, err := resolve(t.Context(), ic, []types.Architecture{types.ParseArchitecture("amd64")}, repo); err == nil {
		t.Fatal("resolve succeeded for a package the repository doesn't have")
	}
}

func writeLock(t *testing.T, data []byte) string {
	t.Helper()
	p := filepath.Join(t.TempDir(), "lock.json")
	if err := os.WriteFile(p, data, 0o644); err != nil {
		t.Fatal(err)
	}
	return p
}

func TestResolveRejectsIndexSignedByAnotherKey(t *testing.T) {
	repo := newTestRepository(t, "x86_64", testPackages()...)
	other := newTestRepository(t, "x86_64")
	// Serve another key under the configured keyring URL, so the index's
	// signature doesn't verify.
	repo.files[testRepo+"/"+testKeyName] = other.files[testRepo+"/"+testKeyName]
	_, err := resolve(t.Context(), testConfig(), []types.Architecture{types.ParseArchitecture("amd64")}, repo)
	if err == nil || !strings.Contains(err.Error(), "signature") {
		t.Fatalf("resolve() = %v, want a signature verification error", err)
	}
}

func TestBuildLayersRejectsTamperedPackage(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("amd64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	locked, err := resolve(ctx, testConfig(), []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	// Replace bar with a package of the same name and version that the
	// signed index doesn't describe.
	evil := newTestRepository(t, "x86_64", testPackage{
		name: "bar", version: "0.1-r0", origin: "bar", buildDate: testBuildDate,
		files: map[string]string{"usr/": "", "usr/bin/": "", "usr/bin/bar": "evil"},
	})
	u := testRepo + "/x86_64/bar-0.1-r0.apk"
	repo.files[u] = evil.files[u]
	_, err = buildLayers(ctx, locked[amd64].ic, amd64, writeLock(t, locked[amd64].lockData), fetchDir(t, repo, locked[amd64].pkgs), t.TempDir())
	if err == nil || !strings.Contains(err.Error(), "hash mismatch") {
		t.Fatalf("buildLayers() = %v, want a control hash mismatch", err)
	}
}

func TestFromLockRejectsUnsignedPackage(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("amd64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	ic := testConfig()
	locked, err := resolve(ctx, ic, []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	pkgs := slices.Clone(locked[amd64].pkgs)
	pkgs[0].Checksum = "Q1AAAAAAAAAAAAAAAAAAAAAAAAAAAA="
	l := lock.Lock{Version: "v1", Contents: lock.LockContents{Packages: pkgs}}
	data, err := json.Marshal(l)
	if err != nil {
		t.Fatal(err)
	}
	_, err = fromLock(ctx, ic, []types.Architecture{amd64}, l, data, repo)
	if err == nil || !strings.Contains(err.Error(), pkgs[0].Name) {
		t.Fatalf("fromLock() = %v, want an error naming %s", err, pkgs[0].Name)
	}
}

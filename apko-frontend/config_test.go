package main

import (
	"io"
	"net/http"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"chainguard.dev/apko/pkg/build/types"
	ocispecs "github.com/opencontainers/image-spec/specs-go/v1"
)

func TestParseConfig(t *testing.T) {
	ic, err := parseConfig([]byte(`# syntax=example.com/apko-frontend
contents:
  repositories:
    - https://packages.wolfi.dev/os/
  packages:
    - wolfi-base
environment:
  FOO: bar
archs:
  - x86_64
  - arm64
`))
	if err != nil {
		t.Fatal(err)
	}
	if got := ic.Contents.Repositories; !slices.Equal(got, []string{"https://packages.wolfi.dev/os"}) {
		t.Errorf("repositories = %v, want the trailing slash trimmed", got)
	}
	if ic.Environment["FOO"] != "bar" {
		t.Errorf("environment = %v", ic.Environment)
	}
	if got, want := configPlatforms(ic), []ocispecs.Platform{{OS: "linux", Architecture: "amd64"}, {OS: "linux", Architecture: "arm64"}}; !slices.EqualFunc(got, want, platformsEqual) {
		t.Errorf("platforms = %v, want %v", got, want)
	}
}

func platformsEqual(a, b ocispecs.Platform) bool {
	return a.OS == b.OS && a.Architecture == b.Architecture && a.Variant == b.Variant
}

func TestParseConfigErrors(t *testing.T) {
	for _, tc := range []struct {
		name, config, want string
	}{
		{"empty", "", "empty"},
		{"comment only", "# syntax=example.com/apko-frontend\n", "empty"},
		{"unknown field", "contents:\n  pakages: [foo]\n", "pakages"},
		{"include", "include: other.yaml\n", "include is not supported"},
		{"baseimage", "contents:\n  baseimage:\n    image: foo\n", "baseimage is not supported"},
		{"erofs", "format: erofs\n", `format "erofs" is not supported`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, err := parseConfig([]byte(tc.config))
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Errorf("parseConfig() = %v, want an error containing %q", err, tc.want)
			}
		})
	}
}

func TestConfigPlatformsDedupes(t *testing.T) {
	ic := types.ImageConfiguration{Archs: []types.Architecture{"x86_64", "amd64", "armv7"}}
	got := configPlatforms(ic)
	want := []ocispecs.Platform{{OS: "linux", Architecture: "amd64"}, {OS: "linux", Architecture: "arm", Variant: "v7"}}
	if !slices.EqualFunc(got, want, platformsEqual) {
		t.Errorf("configPlatforms() = %v, want %v", got, want)
	}
	if got := configPlatforms(types.ImageConfiguration{}); got != nil {
		t.Errorf("configPlatforms() with no archs = %v, want nil", got)
	}
}

func TestPlatformArch(t *testing.T) {
	for _, tc := range []struct {
		p    ocispecs.Platform
		want string
	}{
		{ocispecs.Platform{OS: "linux", Architecture: "amd64"}, "x86_64"},
		{ocispecs.Platform{OS: "linux", Architecture: "arm64"}, "aarch64"},
		{ocispecs.Platform{OS: "linux", Architecture: "arm", Variant: "v7"}, "armv7"},
		{ocispecs.Platform{OS: "linux", Architecture: "arm", Variant: "v6"}, "armhf"},
		{ocispecs.Platform{OS: "linux", Architecture: "arm"}, "armv7"},
		{ocispecs.Platform{OS: "linux", Architecture: "386"}, "x86"},
		{ocispecs.Platform{OS: "linux", Architecture: "riscv64"}, "riscv64"},
	} {
		if got := platformArch(tc.p).ToAPK(); got != tc.want {
			t.Errorf("platformArch(%v) = %s, want %s", tc.p, got, tc.want)
		}
	}
}

func TestLocalInputs(t *testing.T) {
	ic := types.ImageConfiguration{Contents: types.ImageContents{
		Keyring:           []string{"https://packages.wolfi.dev/os/wolfi-signing.rsa.pub", "./melange.rsa.pub", "keys/../melange.rsa.pub"},
		Repositories:      []string{"https://packages.wolfi.dev/os", "./packages"},
		BuildRepositories: []string{"@local local-repo"},
	}}
	got, err := localInputs(ic, []types.Architecture{"amd64", "arm64"})
	if err != nil {
		t.Fatal(err)
	}
	want := []string{
		"local-repo/aarch64/APKINDEX.tar.gz",
		"local-repo/x86_64/APKINDEX.tar.gz",
		"melange.rsa.pub",
		"packages/aarch64/APKINDEX.tar.gz",
		"packages/x86_64/APKINDEX.tar.gz",
	}
	if !slices.Equal(got, want) {
		t.Errorf("localInputs() = %v, want %v", got, want)
	}

	ic.Contents.Keyring = []string{"../outside.rsa.pub"}
	if _, err := localInputs(ic, []types.Architecture{"amd64"}); err == nil {
		t.Error("localInputs() accepted a path outside the build context")
	}
}

func TestContextPath(t *testing.T) {
	for _, tc := range []struct {
		in, want string
	}{
		{"./packages/x86_64/foo-1.apk", "packages/x86_64/foo-1.apk"},
		{contextDir + "/packages/x86_64/foo-1.apk", "packages/x86_64/foo-1.apk"},
		{"file://" + contextDir + "/keys/a.rsa.pub", "keys/a.rsa.pub"},
	} {
		got, err := contextPath(tc.in)
		if err != nil || got != tc.want {
			t.Errorf("contextPath(%q) = %q, %v; want %q", tc.in, got, err, tc.want)
		}
	}
	for _, in := range []string{"/etc/passwd", "../x", contextDir + "/../x"} {
		if got, err := contextPath(in); err == nil {
			t.Errorf("contextPath(%q) = %q, want an error", in, got)
		}
	}
}

func TestDirTransport(t *testing.T) {
	dir := t.TempDir()
	const u = "https://packages.wolfi.dev/os/x86_64/APKINDEX.tar.gz"
	key, err := fetchKey(u)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, key), []byte("index"), 0o644); err != nil {
		t.Fatal(err)
	}
	c := &http.Client{Transport: dirTransport{dir: dir}}

	resp, err := c.Get(u)
	if err != nil {
		t.Fatal(err)
	}
	body, err := io.ReadAll(resp.Body)
	resp.Body.Close()
	if err != nil || resp.StatusCode != http.StatusOK || string(body) != "index" {
		t.Errorf("GET %s = %d %q, %v; want 200 %q", u, resp.StatusCode, body, err, "index")
	}

	resp, err = c.Head(u)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusOK || resp.ContentLength != int64(len("index")) {
		t.Errorf("HEAD %s = %d with length %d, want 200 with length %d", u, resp.StatusCode, resp.ContentLength, len("index"))
	}

	resp, err = c.Get("https://packages.wolfi.dev/os/x86_64/missing.apk")
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusNotFound {
		t.Errorf("GET of an unfetched URL = %d, want 404", resp.StatusCode)
	}

	resp, err = c.Post(u, "text/plain", strings.NewReader("x"))
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusMethodNotAllowed {
		t.Errorf("POST = %d, want 405", resp.StatusCode)
	}
}

func TestDemoConfigsParse(t *testing.T) {
	files, err := filepath.Glob("demo/*.apko.yaml")
	if err != nil {
		t.Fatal(err)
	}
	if len(files) == 0 {
		t.Fatal("found no demo configurations")
	}
	for _, f := range files {
		data, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		ic, err := parseConfig(data)
		if err != nil {
			t.Errorf("%s: %v", f, err)
			continue
		}
		if err := ic.Validate(); err != nil {
			t.Errorf("%s: %v", f, err)
		}
	}
}

package main

import (
	"bytes"
	"errors"
	"io"
	"io/fs"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"chainguard.dev/apko/pkg/apk/expandapk"
	"chainguard.dev/apko/pkg/build/types"
)

func TestFetchAPK(t *testing.T) {
	ctx := t.Context()
	amd64 := types.ParseArchitecture("amd64")
	repo := newTestRepository(t, "x86_64", testPackages()...)
	locked, err := resolve(ctx, testConfig(), []types.Architecture{amd64}, repo)
	if err != nil {
		t.Fatalf("resolve: %v", err)
	}
	c := &http.Client{Transport: repo}
	var bar, base string
	var barSum string
	for _, p := range locked[amd64].pkgs {
		switch p.Name {
		case "bar":
			bar, barSum = p.URL, p.Checksum
		case "base":
			base = p.URL
		}
	}

	t.Run("verified", func(t *testing.T) {
		out := filepath.Join(t.TempDir(), "pkg")
		if err := fetchAPK(ctx, c, bar, barSum, out); err != nil {
			t.Fatalf("fetchAPK: %v", err)
		}
		got, err := os.ReadFile(out)
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(got, repo.files[bar]) {
			t.Error("the fetched file differs from the served package")
		}
	})

	for _, tc := range []struct {
		name, url, checksum, want string
		serve                     []byte
	}{{
		name: "wrong checksum", url: bar, checksum: "Q1AAAAAAAAAAAAAAAAAAAAAAAAAAAA=",
		want: "control section checksum",
	}, {
		// bar's signature and control sections with base's data section:
		// the checksum matches the index, but the data doesn't match the
		// control section's datahash.
		name: "replaced data", url: bar, checksum: barSum,
		serve: spliceData(t, repo.files[bar], repo.files[base]),
		want:  "data section SHA-256",
	}, {
		name: "not found", url: testRepo + "/x86_64/missing-1.0-r0.apk", checksum: barSum,
		want: "404",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			if tc.serve != nil {
				orig := repo.files[tc.url]
				repo.files[tc.url] = tc.serve
				t.Cleanup(func() { repo.files[tc.url] = orig })
			}
			out := filepath.Join(t.TempDir(), "pkg")
			err := fetchAPK(ctx, c, tc.url, tc.checksum, out)
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("fetchAPK() = %v, want an error containing %q", err, tc.want)
			}
			entries, err := os.ReadDir(filepath.Dir(out))
			if err != nil {
				t.Fatal(err)
			}
			if len(entries) != 0 {
				t.Errorf("fetchAPK left %v behind; a failed fetch must write nothing", entries)
			}
			if _, err := os.Stat(out); !errors.Is(err, fs.ErrNotExist) {
				t.Errorf("stat %s = %v, want not exist", out, err)
			}
		})
	}
}

// spliceData returns the signature and control sections of a with the data
// section of b.
func spliceData(t *testing.T, a, b []byte) []byte {
	t.Helper()
	pa, err := expandapk.Split(bytes.NewReader(a))
	if err != nil {
		t.Fatal(err)
	}
	pb, err := expandapk.Split(bytes.NewReader(b))
	if err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	for _, r := range append(pa[:len(pa)-1], pb[len(pb)-1]) {
		if _, err := io.Copy(&out, r); err != nil {
			t.Fatal(err)
		}
	}
	return out.Bytes()
}

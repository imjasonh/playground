package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"crypto"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/pem"
	"fmt"
	"io"
	"maps"
	"net/http"
	"slices"
	"strings"
	"sync"
	"testing"
)

const (
	testRepo      = "https://repo.test/os"
	testKeyName   = "test.rsa.pub"
	testBuildDate = 1700000000
)

// testPackage describes an apk package for a test repository.
type testPackage struct {
	name, version, origin string
	depends               []string
	// files maps paths to contents. Paths ending in "/" are directories.
	files map[string]string
	// buildDate is the package's build time, in seconds since the epoch.
	buildDate int64
}

// testRepository is a signed apk repository served from memory.
type testRepository struct {
	key   *rsa.PrivateKey
	files map[string][]byte

	mu        sync.Mutex
	requested []string
}

func newTestRepository(t *testing.T, arch string, pkgs ...testPackage) *testRepository {
	t.Helper()
	key, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		t.Fatal(err)
	}
	pub, err := x509.MarshalPKIXPublicKey(&key.PublicKey)
	if err != nil {
		t.Fatal(err)
	}
	r := &testRepository{key: key, files: map[string][]byte{
		testRepo + "/" + testKeyName: pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: pub}),
	}}
	var index strings.Builder
	for _, p := range pkgs {
		apk, control, installed := r.buildAPK(t, arch, p)
		r.files[fmt.Sprintf("%s/%s/%s-%s.apk", testRepo, arch, p.name, p.version)] = apk
		sum := sha1.Sum(control)
		fmt.Fprintf(&index, "C:Q1%s\nP:%s\nV:%s\nA:%s\nS:%d\nI:%d\nT:%s\nL:MIT\no:%s\nt:%d\n",
			base64.StdEncoding.EncodeToString(sum[:]), p.name, p.version, arch, len(apk), installed, p.name, p.origin, p.buildDate)
		if len(p.depends) > 0 {
			fmt.Fprintf(&index, "D:%s\n", strings.Join(p.depends, " "))
		}
		index.WriteString("\n")
	}
	idx := gzipTar(t, true, map[string]string{"APKINDEX": index.String(), "DESCRIPTION": "test"})
	r.files[testRepo+"/"+arch+"/APKINDEX.tar.gz"] = append(r.signature(t, idx), idx...)
	return r
}

// buildAPK returns an apk file, its control section, and its installed size.
func (r *testRepository) buildAPK(t *testing.T, arch string, p testPackage) ([]byte, []byte, int) {
	t.Helper()
	installed := 0
	for _, c := range p.files {
		installed += len(c)
	}
	data := gzipTar(t, false, p.files)
	dataHash := sha256.Sum256(data)
	info := fmt.Sprintf("pkgname = %s\npkgver = %s\narch = %s\nsize = %d\norigin = %s\nbuilddate = %d\nlicense = MIT\ndatahash = %s\n",
		p.name, p.version, arch, installed, p.origin, p.buildDate, hex.EncodeToString(dataHash[:]))
	for _, d := range p.depends {
		info += "depend = " + d + "\n"
	}
	control := gzipTar(t, true, map[string]string{".PKGINFO": info})
	return slices.Concat(r.signature(t, control), control, data), control, installed
}

// signature returns the signature section that signs a gzip stream, as
// abuild-sign writes it.
func (r *testRepository) signature(t *testing.T, signed []byte) []byte {
	t.Helper()
	sum := sha1.Sum(signed)
	sig, err := rsa.SignPKCS1v15(rand.Reader, r.key, crypto.SHA1, sum[:])
	if err != nil {
		t.Fatal(err)
	}
	return gzipTar(t, true, map[string]string{".SIGN.RSA." + testKeyName: string(sig)})
}

// gzipTar returns a gzipped tar of files, in path order. apk's signature and
// control sections omit the end-of-archive marker, so that the sections
// concatenate into one tar stream.
func gzipTar(t *testing.T, cut bool, files map[string]string) []byte {
	t.Helper()
	var buf bytes.Buffer
	zw := gzip.NewWriter(&buf)
	tw := tar.NewWriter(zw)
	for _, name := range slices.Sorted(maps.Keys(files)) {
		hdr := &tar.Header{Name: name, Mode: 0o644, Typeflag: tar.TypeReg, Size: int64(len(files[name]))}
		if !cut {
			// Data sections record each file's checksum, as abuild does.
			sum := sha1.Sum([]byte(files[name]))
			hdr.PAXRecords = map[string]string{"APK-TOOLS.checksum.SHA1": hex.EncodeToString(sum[:])}
		}
		if strings.HasSuffix(name, "/") {
			hdr = &tar.Header{Name: name, Mode: 0o755, Typeflag: tar.TypeDir}
		}
		if err := tw.WriteHeader(hdr); err != nil {
			t.Fatal(err)
		}
		if _, err := io.WriteString(tw, files[name]); err != nil {
			t.Fatal(err)
		}
	}
	var err error
	if cut {
		err = tw.Flush()
	} else {
		err = tw.Close()
	}
	if err != nil {
		t.Fatal(err)
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

// RoundTrip serves the repository's files and records each request.
func (r *testRepository) RoundTrip(req *http.Request) (*http.Response, error) {
	r.mu.Lock()
	r.requested = append(r.requested, req.URL.String())
	r.mu.Unlock()
	data, ok := r.files[req.URL.String()]
	if !ok {
		return textResponse(req, http.StatusNotFound, "not found"), nil
	}
	return &http.Response{
		StatusCode:    http.StatusOK,
		Header:        http.Header{},
		ContentLength: int64(len(data)),
		Body:          io.NopCloser(bytes.NewReader(data)),
		Request:       req,
	}, nil
}

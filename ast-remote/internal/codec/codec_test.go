package codec

import (
	"bytes"
	"compress/gzip"
	"os"
	"path/filepath"
	"testing"
)

func TestRoundTripGo(t *testing.T) {
	src := []byte(`package demo

import "fmt"

func Hello(name string) string {
	return fmt.Sprintf("hi %s", name)
}
`)
	res, err := EncodeFileOpts("demo.go", src, EncodeOptions{NoAdaptive: true})
	if err != nil {
		t.Fatal(err)
	}
	if res.Lang != "go" {
		t.Fatalf("lang=%q", res.Lang)
	}
	if res.Encoding != EncodingAST {
		t.Fatalf("encoding=%s", res.Encoding)
	}
	out, err := Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(out, src) {
		t.Fatalf("round-trip mismatch\nwant:\n%s\ngot:\n%s", src, out)
	}
}

func TestRoundTripJS(t *testing.T) {
	src := []byte(`export function add(a, b) {
  return a + b;
}
`)
	res, err := EncodeFileOpts("math.js", src, EncodeOptions{NoAdaptive: true})
	if err != nil {
		t.Fatal(err)
	}
	out, err := Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(out, src) {
		t.Fatalf("js round-trip mismatch")
	}
}

func TestFallbackRaw(t *testing.T) {
	src := []byte("not a programming language file")
	res, err := EncodeFileOpts("notes.txt", src, EncodeOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if res.Encoding != EncodingRaw {
		t.Fatalf("expected raw fallback, got %s", res.Encoding)
	}
	out, err := Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(out, src) {
		t.Fatalf("raw round-trip mismatch")
	}
}

func TestDictRoundTrip(t *testing.T) {
	src := []byte(`package demo

func Hello() string { return "hi" }
`)
	res, err := EncodeFileOpts("demo.go", src, EncodeOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if res.ASTDictSize == 0 && res.RawDictSize == 0 {
		t.Fatal("expected language dict candidates for Go")
	}
	out, err := Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(out, src) {
		t.Fatalf("adaptive round-trip mismatch")
	}
}

func TestAdaptiveNeverWorseThanGzip(t *testing.T) {
	src := []byte(`package demo

func Hello(name string) string {
	return "hi " + name
}
`)
	res, err := EncodeFileOpts("demo.go", src, EncodeOptions{})
	if err != nil {
		t.Fatal(err)
	}
	var gzBuf bytes.Buffer
	zw, err := gzip.NewWriterLevel(&gzBuf, gzip.BestCompression)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := zw.Write(src); err != nil {
		t.Fatal(err)
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	if res.PayloadSize > gzBuf.Len() {
		t.Fatalf("adaptive %d > gzip %d", res.PayloadSize, gzBuf.Len())
	}
}

func TestEncodeFile(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "x.go")
	src := []byte("package x\n")
	if err := os.WriteFile(path, src, 0o644); err != nil {
		t.Fatal(err)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	res, err := EncodeFile(path, data)
	if err != nil {
		t.Fatal(err)
	}
	out, err := Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(out, src) {
		t.Fatal("EncodeFile round-trip failed")
	}
}


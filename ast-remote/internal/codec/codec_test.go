package codec_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/codec"
)

func TestRoundTripGoLeaves(t *testing.T) {
	src := []byte(`package main

import "fmt"

func main() {
	fmt.Println("hello", 1+2)
}
`)
	res, err := codec.EncodeFileOpts("main.go", src, codec.EncodeOptions{NoAdaptive: true})
	if err != nil {
		t.Fatal(err)
	}
	if res.Encoding != codec.EncodingASTGzip {
		t.Fatalf("expected ast-gzip, got %s (%s)", res.Encoding, res.SkippedReason)
	}
	if res.Mode != "leaves" {
		t.Fatalf("expected leaves mode, got %s", res.Mode)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatalf("mismatch:\n got %q\nwant %q", back, src)
	}
}

func TestRoundTripGoFullTree(t *testing.T) {
	src := []byte("package p\n\nfunc F() int { return 1 }\n")
	res, err := codec.EncodeFileOpts("p.go", src, codec.EncodeOptions{
		PreferFullTree: true,
		NoAdaptive:     true,
	})
	if err != nil {
		t.Fatal(err)
	}
	if res.Mode != "full-tree" {
		t.Fatalf("mode=%s", res.Mode)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatal("mismatch")
	}
}

func TestAdaptivePrefersGzipWhenSmaller(t *testing.T) {
	src := []byte("package p\n")
	res, err := codec.EncodeFile("p.go", src)
	if err != nil {
		t.Fatal(err)
	}
	// Tiny file: gzip(raw) almost always beats AST framing.
	if res.Encoding != codec.EncodingRaw {
		t.Fatalf("expected adaptive raw fallback, got %s payload=%d gzip=%d",
			res.Encoding, res.PayloadSize, res.GzipRawSize)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatal("mismatch")
	}
}

func TestRoundTripPython(t *testing.T) {
	src := []byte("def greet(name):\n    return f\"hi {name}\"\n\nprint(greet('x'))\n")
	res, err := codec.EncodeFileOpts("hi.py", src, codec.EncodeOptions{NoAdaptive: true})
	if err != nil {
		t.Fatal(err)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatalf("mismatch")
	}
}

func TestFallbackUnsupported(t *testing.T) {
	src := []byte("not source")
	res, err := codec.EncodeFile("readme.txt", src)
	if err != nil {
		t.Fatal(err)
	}
	if res.Encoding != codec.EncodingRaw {
		t.Fatalf("expected raw, got %s", res.Encoding)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatal("mismatch")
	}
}

func TestRoundTripFixtures(t *testing.T) {
	root := filepath.Join("..", "..", "testdata", "corpus")
	entries, err := os.ReadDir(root)
	if err != nil {
		t.Skip(err)
	}
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		path := filepath.Join(root, e.Name())
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		for _, opts := range []codec.EncodeOptions{
			{NoAdaptive: true},
			{PreferFullTree: true, NoAdaptive: true},
			{},
		} {
			res, err := codec.EncodeFileOpts(path, src, opts)
			if err != nil {
				t.Fatalf("%s: %v", e.Name(), err)
			}
			back, err := codec.Decode(res.Encoding, res.Payload)
			if err != nil {
				t.Fatalf("%s decode: %v", e.Name(), err)
			}
			if string(back) != string(src) {
				t.Fatalf("%s round-trip mismatch (mode=%s enc=%s)", e.Name(), res.Mode, res.Encoding)
			}
		}
	}
}

func TestLeavesSmallerThanFullTree(t *testing.T) {
	src, err := os.ReadFile(filepath.Join("..", "..", "testdata", "corpus", "repetitive.go"))
	if err != nil {
		t.Skip(err)
	}
	leaf, err := codec.EncodeFileOpts("repetitive.go", src, codec.EncodeOptions{
		NoAdaptive:          true,
		AlsoMeasureFullTree: true,
	})
	if err != nil {
		t.Fatal(err)
	}
	full, err := codec.EncodeFileOpts("repetitive.go", src, codec.EncodeOptions{
		PreferFullTree: true,
		NoAdaptive:     true,
	})
	if err != nil {
		t.Fatal(err)
	}
	if leaf.PayloadSize >= full.PayloadSize {
		t.Fatalf("expected leaves (%d) < full-tree (%d)", leaf.PayloadSize, full.PayloadSize)
	}
	if leaf.LeafASTSize == 0 || leaf.FullASTSize == 0 {
		t.Fatalf("expected both sizes measured: leaf=%d full=%d", leaf.LeafASTSize, leaf.FullASTSize)
	}
}

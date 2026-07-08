package codec_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/ast-remote/internal/codec"
)

func TestRoundTripGoSubst(t *testing.T) {
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
	if res.Mode != "subst" {
		t.Fatalf("expected subst mode, got %s", res.Mode)
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatalf("mismatch:\n got %q\nwant %q", back, src)
	}
}

func TestRoundTripGoLeaves(t *testing.T) {
	src := []byte(`package main

import "fmt"

func main() {
	fmt.Println("hello", 1+2)
}
`)
	res, err := codec.EncodeFileOpts("main.go", src, codec.EncodeOptions{
		PreferLeaves: true,
		NoAdaptive:   true,
	})
	if err != nil {
		t.Fatal(err)
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

func TestAdaptiveNeverWorseThanGzip(t *testing.T) {
	src := []byte("package p\n")
	res, err := codec.EncodeFile("p.go", src)
	if err != nil {
		t.Fatal(err)
	}
	if res.PayloadSize > res.GzipRawSize {
		t.Fatalf("adaptive stored %d > gzip %d (enc=%s)", res.PayloadSize, res.GzipRawSize, res.Encoding)
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
			{PreferLeaves: true, NoAdaptive: true},
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

func TestSubstCompetitiveWithGzip(t *testing.T) {
	src, err := os.ReadFile(filepath.Join("..", "..", "testdata", "corpus", "repetitive.go"))
	if err != nil {
		t.Skip(err)
	}
	res, err := codec.EncodeFileOpts("repetitive.go", src, codec.EncodeOptions{
		NoAdaptive:          true,
		AlsoMeasureFullTree: true,
	})
	if err != nil {
		t.Fatal(err)
	}
	// AST2 subst should be within ~5% of gzip on repetitive Go.
	if res.LeafASTSize > res.GzipRawSize*105/100 {
		t.Fatalf("subst+gzip %d much larger than gzip %d", res.LeafASTSize, res.GzipRawSize)
	}
	if res.FullASTSize > 0 && res.LeafASTSize >= res.FullASTSize {
		t.Fatalf("expected subst (%d) < full-tree (%d)", res.LeafASTSize, res.FullASTSize)
	}
}

func TestAdaptiveBeatsOrTiesGzipOnGitdbSample(t *testing.T) {
	root := filepath.Join("..", "..", "..", "gitdb")
	path := filepath.Join(root, "main.go")
	src, err := os.ReadFile(path)
	if err != nil {
		t.Skip(err)
	}
	res, err := codec.EncodeFile(path, src)
	if err != nil {
		t.Fatal(err)
	}
	if res.PayloadSize > res.GzipRawSize {
		t.Fatalf("stored %d > gzip %d", res.PayloadSize, res.GzipRawSize)
	}
	if res.RawDictSize == 0 {
		t.Fatal("expected raw-dict candidate for Go")
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	if err != nil {
		t.Fatal(err)
	}
	if string(back) != string(src) {
		t.Fatal("mismatch")
	}
}

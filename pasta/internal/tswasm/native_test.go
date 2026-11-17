//go:build cgo && !purego

package tswasm

import (
	"bytes"
	"context"
	"errors"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"
)

// nativeSamples has one input per native grammar, so each is compared
// even when the module has no file in that language.
var nativeSamples = map[string]string{
	"go":         "package p\n\nfunc F(a, b int) error { if a > b { return nil }; return F(b, a) }\n",
	"python":     "def f(x):\n    return [y for y in x if y]\n",
	"rust":       "fn main() { let v: Vec<u8> = vec![1, 2]; println!(\"{:?}\", v); }\n",
	"javascript": "export const f = async (a) => { await a?.b; return `${a}`; };\n",
	"typescript": "export function f<T>(a: T[]): T | undefined { return a[0]; }\n",
	"tsx":        "const App = (p: {n: number}) => <div className=\"a\">{p.n}</div>;\n",
	"yaml":       "a:\n  - b: 1\n    c: [x, y]\n",
	"bash":       "for f in *.go; do echo \"$f\" | grep -q x && exit 1; done\n",
	"json":       "{\"a\": [1, true, null, {\"b\": \"c\"}]}\n",
	"c":          "#include <stdio.h>\nint main(void) { printf(\"%d\\n\", 1); return 0; }\n",
	"cpp":        "template <typename T> T f(T a) { return a; }\nauto x = f<int>(1);\n",
	"css":        "a:hover > .b { color: #fff; margin: 0 auto !important; }\n",
	"html":       "<!doctype html><p class=x>hi<br><script>let a = 1;</script>\n",
	"java":       "class A { <T> T f(T a) { return a; } }\n",
	"php":        "<?php function f(array $a): ?int { return $a[0] ?? null; } ?>\n",
	"ruby":       "def f(a) = a.map { |x| x * 2 }\n",
	"swift":      "func f(_ a: [Int]) -> Int? { guard let x = a.first else { return nil }; return x }\n",
	"toml":       "[a]\nb = [1, 2]\nc = { d = \"e\" }\n",
	"hcl":        "resource \"a\" \"b\" {\n  c = [for x in var.d : x]\n}\n",
}

var nativeExts = map[string]string{
	".go": "go", ".py": "python", ".rs": "rust", ".js": "javascript", ".mjs": "javascript",
	".ts": "typescript", ".tsx": "tsx", ".yaml": "yaml", ".yml": "yaml", ".sh": "bash",
	".json": "json", ".c": "c", ".h": "c", ".cc": "cpp", ".cpp": "cpp", ".hpp": "cpp",
	".css": "css", ".html": "html", ".java": "java", ".php": "php", ".rb": "ruby",
	".swift": "swift", ".toml": "toml", ".tf": "hcl", ".hcl": "hcl",
}

// TestNativeMatchesWasm checks that the native grammars build the same
// trees as the embedded wasm module. They differ when a grammar module
// drifts from the version build.sh compiles.
func TestNativeMatchesWasm(t *testing.T) {
	if native == nil {
		t.Fatal("native backend not registered")
	}
	b := native.(*cgoBackend)
	if !slices.Equal(slices.Sorted(maps.Keys(b.langs)), slices.Sorted(maps.Keys(nativeSamples))) {
		t.Fatal("nativeSamples must list exactly the native grammars")
	}

	inputs := map[string][][]byte{}
	for g, s := range nativeSamples {
		inputs[g] = [][]byte{[]byte(s)}
	}
	const perGrammar = 512 << 10
	size := map[string]int{}
	err := filepath.WalkDir("../..", func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if d.Name() == "node_modules" || strings.HasPrefix(d.Name(), ".") && p != "../.." {
				return filepath.SkipDir
			}
			return nil
		}
		g := nativeExts[filepath.Ext(p)]
		if g == "" || size[g] >= perGrammar {
			return nil
		}
		src, err := os.ReadFile(p)
		if err != nil || len(src) > perGrammar/4 {
			return err
		}
		size[g] += len(src)
		inputs[g] = append(inputs[g], src)
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}

	for g, srcs := range inputs {
		t.Logf("%s: %d inputs, %d bytes", g, len(srcs), size[g]+len(nativeSamples[g]))
		for i, src := range srcs {
			got, err := b.parseDump(t.Context(), g, src, ParseOptions{})
			if err != nil {
				t.Fatalf("%s input %d: native: %v", g, i, err)
			}
			want := wasmDump(t, g, src)
			if i == 0 && (!maps.Equal(got.kinds, want.kinds) || !maps.Equal(got.fields, want.fields)) {
				t.Errorf("%s: native symbol or field names differ from wasm", g)
			}
			if got.n != want.n || !bytes.Equal(got.raw, want.raw) {
				t.Errorf("%s input %d (%d bytes): native tree has %d nodes, wasm %d; trees differ",
					g, i, len(src), got.n, want.n)
			}
		}
	}
}

func wasmDump(t *testing.T, grammar string, src []byte) treeDump {
	t.Helper()
	e, err := gpool.acquire()
	if err != nil {
		t.Fatal(err)
	}
	d, err := e.parseDump(t.Context(), ExportName(grammar), src, ParseOptions{})
	gpool.release(e, err != nil)
	if err != nil {
		t.Fatalf("%s: wasm: %v", grammar, err)
	}
	return d
}

func TestNativeFallsBackToWasm(t *testing.T) {
	if native.has("sql") {
		t.Fatal("sql has a native grammar; drop this test's assumption")
	}
	tree, err := Parse(t.Context(), &Language{Grammar: "sql"}, []byte("SELECT a FROM b;\n"), "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if root := tree.RootNode(); root.Type() != "program" || root.HasError() {
		t.Fatalf("sql tree: %s", root.SExpr())
	}
}

func TestNativeParseEmpty(t *testing.T) {
	tree, err := Parse(t.Context(), &Language{Grammar: "go"}, nil, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if got := tree.RootNode().Type(); got != "source_file" {
		t.Fatalf("root = %q, want source_file", got)
	}
}

// TestNativeParseCancel cancels a parse that takes far longer than the
// context allows. Unlike wasm, the native parser stops when ctx ends.
func TestNativeParseCancel(t *testing.T) {
	var src []byte
	for len(src) < 8<<20 {
		src = append(src, "func F() { var x int; _ = x }\n"...)
	}
	src = append([]byte("package p\n"), src...)
	ctx, cancel := context.WithTimeout(t.Context(), time.Millisecond)
	defer cancel()
	start := time.Now()
	_, err := Parse(ctx, &Language{Grammar: "go"}, src, "", ParseOptions{})
	if err == nil {
		t.Skip("parse finished within 1ms")
	}
	if !errors.Is(err, context.DeadlineExceeded) {
		t.Fatalf("err = %v, want context.DeadlineExceeded", err)
	}
	if d := time.Since(start); d > time.Second {
		t.Errorf("canceled parse took %v", d)
	}
}

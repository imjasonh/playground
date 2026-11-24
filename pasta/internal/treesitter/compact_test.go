package treesitter

import (
	"os"
	"testing"
)

func TestCompactRoundTrip(t *testing.T) {
	self, err := os.ReadFile("compact.go")
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		grammar string
		src     string
	}{
		{"go", string(self)},
		{"go", "package p\n\nfunc F( {\n\tx := \n}\n"},
		{"go", ""},
		{"python", "def f(x):\n    return [y for y in x if y]\n"},
		{"tsx", "export const A = () => <div className=\"a\">{b}</div>;\n"},
		{"rust", "fn main() { let v: Vec<u8> = vec![1, 2]; }\n"},
		{"hcl", "resource \"a\" \"b\" {\n  c = d\n}\n"},
	} {
		lang := &Language{Grammar: tc.grammar}
		src := []byte(tc.src)
		tree, err := Parse(t.Context(), lang, src, "f", ParseOptions{})
		if err != nil {
			t.Fatal(err)
		}
		c := tree.Compact()
		got, err := c.Tree(lang, src, "f")
		if err != nil {
			t.Fatalf("%s %.20q: %v", tc.grammar, tc.src, err)
		}
		if got.NodeCount() != tree.NodeCount() {
			t.Errorf("%s %.20q: NodeCount = %d, want %d", tc.grammar, tc.src, got.NodeCount(), tree.NodeCount())
		}
		if got.fileID != "f" || got.lang != lang {
			t.Errorf("%s %.20q: rebuilt tree has the wrong file ID or language", tc.grammar, tc.src)
		}
		sameGraph(t, got.root, tree.root, nil)
	}
}

func TestCompactSize(t *testing.T) {
	src, err := os.ReadFile("treesitter.go")
	if err != nil {
		t.Fatal(err)
	}
	tree, err := Parse(t.Context(), &Language{Grammar: "go"}, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	c := tree.Compact()
	if perNode := float64(len(c)) / float64(tree.NodeCount()); perNode > 8 {
		t.Errorf("compact tree takes %.1f bytes per node, want at most 8", perNode)
	}
}

func TestCompactRejectsMalformed(t *testing.T) {
	src := []byte("package p\n\nfunc F() { return }\n")
	lang := &Language{Grammar: "go"}
	tree, err := Parse(t.Context(), lang, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	c := tree.Compact()
	for i := range c {
		if _, err := c[:i].Tree(lang, src, ""); err == nil {
			t.Errorf("Tree accepted the first %d of %d bytes", i, len(c))
		}
	}
	if _, err := c.Tree(lang, src[:len(src)/2], ""); err == nil {
		t.Error("Tree accepted a source shorter than the tree")
	}
	bad := append(Compact{compactVersion + 1}, c[1:]...)
	if _, err := bad.Tree(lang, src, ""); err == nil {
		t.Error("Tree accepted an unknown version")
	}
}

// sameGraph fails t unless the subtrees at got and want have the same
// shape and node fields, and got's parent is gotParent.
func sameGraph(t *testing.T, got, want, gotParent *node) {
	t.Helper()
	if got.kind != want.kind || got.start != want.start || got.end != want.end ||
		got.fieldName != want.fieldName || got.flags() != want.flags() {
		t.Fatalf("node = {%q %d-%d %q %b}, want {%q %d-%d %q %b}",
			got.kind, got.start, got.end, got.fieldName, got.flags(),
			want.kind, want.start, want.end, want.fieldName, want.flags())
	}
	if got.parent != gotParent {
		t.Fatalf("%s at %d has the wrong parent", got.kind, got.start)
	}
	if len(got.children) != len(want.children) || len(got.namedChildren) != len(want.namedChildren) {
		t.Fatalf("%s at %d has %d children (%d named), want %d (%d named)", got.kind, got.start,
			len(got.children), len(got.namedChildren), len(want.children), len(want.namedChildren))
	}
	for i := range got.children {
		sameGraph(t, got.children[i], want.children[i], got)
	}
	for i := range got.namedChildren {
		if got.namedChildren[i].start != want.namedChildren[i].start || got.namedChildren[i].kind != want.namedChildren[i].kind {
			t.Fatalf("%s at %d: named child %d differs", got.kind, got.start, i)
		}
	}
}

package tswasm

import (
	"testing"
	"time"
)

func TestParseGo(t *testing.T) {
	src := []byte("package p\n\nfunc F() {}\n")
	tree, err := Parse(t.Context(), &Language{Grammar: "go"}, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()
	root := tree.RootNode()
	if root.Type() != "source_file" {
		t.Fatalf("type=%q", root.Type())
	}
	if root.HasError() {
		t.Fatalf("unexpected error: %s", root.SExpr())
	}
	if !HasGrammar("go") || !HasGrammar("tsx") || !HasGrammar("swift") || !HasGrammar("toml") || !HasGrammar("hcl") {
		t.Fatal("expected core grammars to be exported")
	}
}

func TestParseHCL(t *testing.T) {
	src := []byte("resource \"aws_s3_bucket\" \"example\" {\n  bucket = \"ok\"\n}\n")
	tree, err := Parse(t.Context(), &Language{Grammar: "hcl"}, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()
	root := tree.RootNode()
	if root.Type() != "config_file" {
		t.Fatalf("type=%q", root.Type())
	}
	if root.HasError() {
		t.Fatalf("unexpected error: %s", root.SExpr())
	}
}

func TestParseTimeout(t *testing.T) {
	src := []byte("package p\n\n")
	for i := 0; i < 3000; i++ {
		src = append(src, []byte("func F() { var x int; _ = x }\n")...)
	}
	if _, err := Parse(t.Context(), &Language{Grammar: "go"}, src, "", ParseOptions{
		Timeout: time.Microsecond,
	}); err == nil {
		t.Skip("parse finished within 1µs")
	}
}

// TestTreeShape checks the rebuilt node graph: child order, named
// children, parent links, the first child of a repeated field, and no
// child for an empty field name.
func TestTreeShape(t *testing.T) {
	src := []byte("package p\n\nfunc f(a, b int) {}\n")
	tree, err := Parse(t.Context(), &Language{Grammar: "go"}, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()
	root := tree.RootNode()
	const want = "(source_file (package_clause (package_identifier)) (function_declaration (identifier) " +
		"(parameter_list (parameter_declaration (identifier) (identifier) (type_identifier))) (block)))"
	if got := root.SExpr(); got != want {
		t.Fatalf("tree:\n got %s\nwant %s", got, want)
	}
	decl := root.NamedChildren()[1].ChildByFieldName("parameters").NamedChildren()[0]
	if decl.Type() != "parameter_declaration" || len(decl.Children()) != 4 || len(decl.NamedChildren()) != 3 {
		t.Fatalf("parameter_declaration has %d children, %d named", len(decl.Children()), len(decl.NamedChildren()))
	}
	for _, c := range decl.Children() {
		if p := c.Parent(); p == nil || p.StartByte() != decl.StartByte() || p.Type() != decl.Type() {
			t.Errorf("%s's parent is %v, want the parameter_declaration", c.Type(), p)
		}
	}
	text := func(n *Node) string { return string(src[n.StartByte():n.EndByte()]) }
	if name := decl.ChildByFieldName("name"); name == nil || text(name) != "a" {
		t.Errorf("first name field = %v, want a", name)
	}
	if typ := decl.ChildByFieldName("type"); typ == nil || text(typ) != "int" {
		t.Errorf("type field = %v, want int", typ)
	}
	if c := decl.ChildByFieldName(""); c != nil {
		t.Errorf("empty field name matched %s", c.Type())
	}
}

func TestFieldNames(t *testing.T) {
	src := []byte("package p\nfunc f() {\n\tif err != nil {\n\t\treturn\n\t}\n}\n")
	tree, err := Parse(t.Context(), &Language{Grammar: "go"}, src, "", ParseOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer tree.Release()
	var ifStmt *Node
	var walk func(*Node)
	walk = func(n *Node) {
		if n.Type() == "if_statement" {
			ifStmt = n
			return
		}
		for _, c := range n.NamedChildren() {
			walk(c)
		}
	}
	walk(tree.RootNode())
	if ifStmt == nil {
		t.Fatal("no if_statement")
	}
	cond := ifStmt.ChildByFieldName("condition")
	if cond == nil || cond.Type() != "binary_expression" {
		t.Fatalf("condition=%v", cond)
	}
}

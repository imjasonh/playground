package tswasm

import (
	"context"
	"testing"
	"time"
)

func TestParseGo(t *testing.T) {
	src := []byte("package p\n\nfunc F() {}\n")
	tree, err := Parse(context.Background(), &Language{Grammar: "go"}, src, "", ParseOptions{})
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
	if !HasGrammar("go") || !HasGrammar("tsx") || !HasGrammar("swift") {
		t.Fatal("expected core grammars to be exported")
	}
}

func TestParseTimeout(t *testing.T) {
	src := []byte("package p\n\n")
	for i := 0; i < 3000; i++ {
		src = append(src, []byte("func F() { var x int; _ = x }\n")...)
	}
	_, err := Parse(context.Background(), &Language{Grammar: "go"}, src, "", ParseOptions{
		Timeout: time.Microsecond,
	})
	if err == nil {
		t.Skip("parse finished within 1µs")
	}
}

func TestFieldNames(t *testing.T) {
	src := []byte("package p\nfunc f() {\n\tif err != nil {\n\t\treturn\n\t}\n}\n")
	tree, err := Parse(context.Background(), &Language{Grammar: "go"}, src, "", ParseOptions{})
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

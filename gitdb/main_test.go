package main

import (
	"bytes"
	"strings"
	"testing"
)

func TestSplitStatements(t *testing.T) {
	cases := []struct {
		in   string
		want int
	}{
		{"SELECT 1;", 1},
		{"SELECT 1; SELECT 2;", 2},
		{"SELECT 1", 1},
		{"-- a comment; not a split\nSELECT 1;", 1},
		{"SELECT ';' AS x; SELECT 2;", 2},
		{"SELECT \"a;b\";", 1},
		{"  \n  ", 0},
	}
	for _, tc := range cases {
		got := splitStatements(tc.in)
		if len(got) != tc.want {
			t.Errorf("splitStatements(%q) = %d statements, want %d (%q)", tc.in, len(got), tc.want, got)
		}
	}
}

func TestPrinterTable(t *testing.T) {
	p := &printer{format: "table", maxWidth: 0}
	var buf bytes.Buffer
	cols := []string{"name", "n"}
	rows := [][]any{
		{"alice", int64(3)},
		{"bob", int64(10)},
		{nil, int64(0)},
	}
	if err := p.print(&buf, cols, rows); err != nil {
		t.Fatal(err)
	}
	out := buf.String()
	if !strings.Contains(out, "alice") || !strings.Contains(out, "bob") {
		t.Errorf("table output missing rows:\n%s", out)
	}
	if !strings.Contains(out, "name") || !strings.Contains(out, "----") {
		t.Errorf("table output missing header/separator:\n%s", out)
	}
}

func TestPrinterFormats(t *testing.T) {
	cols := []string{"a", "b"}
	rows := [][]any{{"x", int64(1)}, {nil, int64(2)}}

	for _, f := range []string{"csv", "tsv", "json", "md"} {
		var buf bytes.Buffer
		p := &printer{format: f, maxWidth: 0}
		if err := p.print(&buf, cols, rows); err != nil {
			t.Fatalf("format %s: %v", f, err)
		}
		if buf.Len() == 0 {
			t.Errorf("format %s produced no output", f)
		}
	}

	var buf bytes.Buffer
	p := &printer{format: "json", maxWidth: 0}
	if err := p.print(&buf, cols, rows); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(buf.String(), "\"a\"") {
		t.Errorf("json missing key: %s", buf.String())
	}
}

func TestPrinterTruncate(t *testing.T) {
	p := &printer{format: "table", maxWidth: 5}
	if got := p.truncate("abcdefghij"); len([]rune(got)) != 5 {
		t.Errorf("truncate width = %d, want 5 (%q)", len([]rune(got)), got)
	}
	if got := p.truncate("abc"); got != "abc" {
		t.Errorf("short string changed: %q", got)
	}
}

func TestUnknownFormat(t *testing.T) {
	p := &printer{format: "nope"}
	var buf bytes.Buffer
	if err := p.print(&buf, []string{"a"}, nil); err == nil {
		t.Errorf("expected error for unknown format")
	}
}

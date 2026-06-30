package main

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/ocidb/internal/tables"
)

func TestSplitQueryFile(t *testing.T) {
	title, sqlText := splitQueryFile("-- Hello world\n--  second line\nSELECT 1;\nSELECT 2;\n")
	if title != "Hello world second line" {
		t.Errorf("title = %q", title)
	}
	if sqlText != "SELECT 1;\nSELECT 2;" {
		t.Errorf("sql = %q", sqlText)
	}
}

func TestLoadQueriesParsesEmbeddedSQL(t *testing.T) {
	qs, err := loadQueries()
	if err != nil {
		t.Fatalf("loadQueries: %v", err)
	}
	if len(qs) != 14 {
		t.Fatalf("loaded %d queries, want 14", len(qs))
	}
	for _, q := range qs {
		if strings.TrimSpace(q.title) == "" {
			t.Errorf("query has empty title: %+v", q)
		}
		if strings.TrimSpace(q.sql) == "" {
			t.Errorf("query %q has empty SQL", q.title)
		}
		if strings.HasPrefix(strings.TrimSpace(q.sql), "--") {
			t.Errorf("query %q still has leading comment in body: %q", q.title, q.sql)
		}
	}
}

func TestDisplaySchema(t *testing.T) {
	out := displaySchema(tables.Schema("image"))
	if !strings.HasPrefix(out, "CREATE TABLE image(") {
		t.Errorf("schema should start with the CREATE TABLE line, got:\n%s", out)
	}
	if strings.Contains(out, "\t") {
		t.Errorf("formatted schema should not contain tabs:\n%s", out)
	}
	for _, line := range strings.Split(out, "\n")[1:] {
		if line == ")" || strings.HasPrefix(line, ")") {
			continue
		}
		if !strings.HasPrefix(line, "  ") {
			t.Errorf("column line not indented: %q", line)
		}
	}
}

func TestCellString(t *testing.T) {
	cases := []struct {
		in   any
		want string
	}{
		{nil, ""},
		{int64(42), "42"},
		{"hello", "hello"},
		{[]byte("bytes"), "bytes"},
		{float64(1.5), "1.5"},
		{true, "1"},
		{false, "0"},
	}
	for _, c := range cases {
		if got := cellString(c.in); got != c.want {
			t.Errorf("cellString(%v) = %q, want %q", c.in, got, c.want)
		}
	}
}

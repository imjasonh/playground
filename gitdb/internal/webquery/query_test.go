package webquery

import (
	"context"
	"database/sql"
	"testing"

	_ "modernc.org/sqlite"
)

func TestRun(t *testing.T) {
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	db.SetMaxOpenConns(1)

	result, err := Run(context.Background(), db, `
		SELECT 7 AS n, 'hello' AS text, x'0001' AS data, NULL AS empty_value
		UNION ALL
		SELECT 8, 'later', x'02', NULL
	`, 1)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := len(result.Rows), 1; got != want {
		t.Fatalf("rows = %d, want %d", got, want)
	}
	if !result.Truncated {
		t.Fatal("expected truncated result")
	}
	if got, want := result.Rows[0][0], int64(7); got != want {
		t.Errorf("integer = %#v, want %#v", got, want)
	}
	if got, want := result.Rows[0][2], "base64:AAE="; got != want {
		t.Errorf("blob = %#v, want %#v", got, want)
	}
	if result.Rows[0][3] != nil {
		t.Errorf("null = %#v, want nil", result.Rows[0][3])
	}
}

func TestRunRejectsEmptyQuery(t *testing.T) {
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()

	if _, err := Run(context.Background(), db, "  ", 10); err == nil {
		t.Fatal("expected empty-query error")
	}
}

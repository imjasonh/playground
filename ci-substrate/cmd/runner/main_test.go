package main

import (
	"os"
	"path/filepath"
	"testing"
)

func TestIdentity(t *testing.T) {
	file := filepath.Join(t.TempDir(), "name")
	if err := os.WriteFile(file, []byte("ci-runner-3\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	empty := filepath.Join(t.TempDir(), "empty")
	if err := os.WriteFile(empty, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	hostname, err := os.Hostname()
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		id, file, want string
		wantErr        bool
	}{
		{id: "explicit", file: file, want: "explicit"},
		{file: file, want: "ci-runner-3"},
		{file: empty, wantErr: true},
		{file: filepath.Join(t.TempDir(), "missing"), wantErr: true},
		{want: hostname},
	} {
		got, err := identity(tc.id, tc.file)
		if (err != nil) != tc.wantErr {
			t.Errorf("identity(%q, %q) err = %v, wantErr %v", tc.id, tc.file, err, tc.wantErr)
		}
		if got != tc.want {
			t.Errorf("identity(%q, %q) = %q, want %q", tc.id, tc.file, got, tc.want)
		}
	}
}

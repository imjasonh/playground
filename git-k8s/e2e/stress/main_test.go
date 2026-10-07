package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestLoadEnv(t *testing.T) {
	path := filepath.Join(t.TempDir(), "env")
	const full = "# Written by setup.sh.\nSTATE=/tmp/s\nCLUSTER=gk\nCONTEXT=kind-gk\nPASSWORD='secret'\nCLUSTER_URL=\"http://172.18.0.1:18881\"\nHOST_URL=http://127.0.0.1:18881\nMOD_PORT=18882\n"
	if err := os.WriteFile(path, []byte(full), 0o644); err != nil {
		t.Fatal(err)
	}
	env, err := loadEnv(path)
	if err != nil {
		t.Fatal(err)
	}
	if env["PASSWORD"] != "secret" || env["CLUSTER_URL"] != "http://172.18.0.1:18881" || env["MOD_PORT"] != "18882" {
		t.Errorf("env = %v", env)
	}

	if err := os.WriteFile(path, []byte(strings.Replace(full, "MOD_PORT=18882\n", "", 1)), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := loadEnv(path); err == nil || !strings.Contains(err.Error(), "MOD_PORT") {
		t.Errorf("loadEnv without MOD_PORT: %v, want an error that names it", err)
	}
	if _, err := loadEnv(filepath.Join(t.TempDir(), "env")); err == nil || !strings.Contains(err.Error(), "run setup.sh first") {
		t.Errorf("loadEnv of a missing file: %v, want an error that says to run setup.sh", err)
	}
}

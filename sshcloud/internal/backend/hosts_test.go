package backend

import (
	"os"
	"path/filepath"
	"testing"
)

func TestParseHostsSpec(t *testing.T) {
	t.Parallel()
	m, err := ParseHostsSpec("a=http://127.0.0.1:8080,b=http://127.0.0.1:8081")
	if err != nil || len(m) != 2 {
		t.Fatalf("got %#v err=%v", m, err)
	}
	if m["a"].BaseURL != "http://127.0.0.1:8080" {
		t.Fatalf("a = %q", m["a"].BaseURL)
	}
	m, err = ParseHostsSpec("a=http://10.0.0.1:8080\nb=http://10.0.0.2:8080\n")
	if err != nil || len(m) != 2 {
		t.Fatalf("multiline: %#v err=%v", m, err)
	}
	if _, err := ParseHostsSpec("nocolon"); err == nil {
		t.Fatal("expected error")
	}
}

func TestHostSetReplaceAndDefault(t *testing.T) {
	t.Parallel()
	hs := NewHostSet(map[string]*AgentClient{
		"host-a": {BaseURL: "http://a"},
	}, "host-a")
	if hs.DefaultHost() != "host-a" || hs.Len() != 1 {
		t.Fatalf("init: default=%s len=%d", hs.DefaultHost(), hs.Len())
	}
	hs.Replace(map[string]*AgentClient{
		"host-b": {BaseURL: "http://b"},
	})
	if _, ok := hs.Get("host-a"); ok {
		t.Fatal("stale host-a")
	}
	c, ok := hs.Get("host-b")
	if !ok || c.BaseURL != "http://b" {
		t.Fatalf("host-b: %#v ok=%v", c, ok)
	}
	if hs.DefaultHost() != "host-b" {
		t.Fatalf("fallback default = %q", hs.DefaultHost())
	}
}

func TestLoadHostsFile(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	p := filepath.Join(dir, "hosts")
	if err := os.WriteFile(p, []byte("z=http://127.0.0.1:9\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	m, err := LoadHostsFile(p)
	if err != nil || m["z"].BaseURL != "http://127.0.0.1:9" {
		t.Fatalf("got %#v err=%v", m, err)
	}
}

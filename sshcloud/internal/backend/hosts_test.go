package backend

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
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

func TestCandidatesBestFitAndSkipCordoned(t *testing.T) {
	t.Parallel()
	host := func(usedMem int, cordoned bool) *httptest.Server {
		return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if r.URL.Path != "/v1/host/capacity" {
				http.NotFound(w, r)
				return
			}
			_ = json.NewEncoder(w).Encode(map[string]any{
				"total":    map[string]int{"vcpus": 4, "mem_mib": 4096},
				"used":     map[string]int{"vcpus": 1, "mem_mib": usedMem},
				"reserved": map[string]int{"vcpus": 0, "mem_mib": 0},
				"cordoned": cordoned,
			})
		}))
	}
	a := host(3000, false)
	b := host(1000, false)
	c := host(3500, true)
	defer a.Close()
	defer b.Close()
	defer c.Close()
	hosts := NewHostSet(map[string]*AgentClient{
		"a": {BaseURL: a.URL, InsecureLoopback: true},
		"b": {BaseURL: b.URL, InsecureLoopback: true},
		"c": {BaseURL: c.URL, InsecureLoopback: true},
	}, "")
	candidates, err := hosts.Candidates(context.Background(), "tiny", nil)
	if err != nil {
		t.Fatal(err)
	}
	if len(candidates) != 2 || candidates[0].ID != "a" || candidates[1].ID != "b" {
		t.Fatalf("candidates %+v", candidates)
	}
}

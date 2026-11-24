package main

import (
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"sync"
	"testing"
)

func TestAuthorization(t *testing.T) {
	dir := t.TempDir()
	write := func(name, content string) string {
		p := filepath.Join(dir, name)
		if err := os.WriteFile(p, []byte(content), 0o600); err != nil {
			t.Fatal(err)
		}
		return p
	}
	header := write("header", "Basic dXNlcjpwYXNz\n")
	token := write("token", "tok\n")
	empty := write("empty", "")
	missing := filepath.Join(dir, "missing")

	for _, tc := range []struct {
		name, header, token, want string
	}{
		{"header first", header, token, "Basic dXNlcjpwYXNz"},
		{"token", missing, token, "Bearer tok"},
		{"empty header", empty, token, "Bearer tok"},
		{"neither", missing, missing, ""},
		{"no flags", "", "", ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := authorization(tc.header, tc.token)
			if err != nil || got != tc.want {
				t.Errorf("authorization() = %q, %v; want %q", got, err, tc.want)
			}
		})
	}
}

func TestAuthClientSendsCredentialsOnlyToThePackageHost(t *testing.T) {
	var mu sync.Mutex
	seen := map[string]string{}
	other := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		seen["other"] = r.Header.Get("Authorization")
		mu.Unlock()
		w.Write([]byte("ok"))
	}))
	defer other.Close()
	repo := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		seen["repo"] = r.Header.Get("Authorization")
		mu.Unlock()
		http.Redirect(w, r, other.URL+"/blob", http.StatusFound)
	}))
	defer repo.Close()

	c, err := authClient(repo.URL+"/x86_64/foo.apk", "Basic secret")
	if err != nil {
		t.Fatal(err)
	}
	resp, err := c.Get(repo.URL + "/x86_64/foo.apk")
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	mu.Lock()
	defer mu.Unlock()
	if seen["repo"] != "Basic secret" {
		t.Errorf("the repository got Authorization %q, want %q", seen["repo"], "Basic secret")
	}
	if got, ok := seen["other"]; !ok || got != "" {
		t.Errorf("the redirect target got Authorization %q (requested: %v), want none", got, ok)
	}
}

package controlauth

import (
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"testing"
)

func TestRequire(t *testing.T) {
	t.Parallel()
	token := "0123456789abcdef0123456789abcdef"
	h := Require(token, http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusNoContent)
	}))

	for name, tc := range map[string]struct {
		auth string
		want int
	}{
		"missing": {},
		"wrong":   {auth: "Bearer wrong"},
		"valid":   {auth: "Bearer " + token, want: http.StatusNoContent},
	} {
		t.Run(name, func(t *testing.T) {
			req := httptest.NewRequest(http.MethodPost, "/", nil)
			req.Header.Set("Authorization", tc.auth)
			rec := httptest.NewRecorder()
			h.ServeHTTP(rec, req)
			want := tc.want
			if want == 0 {
				want = http.StatusUnauthorized
			}
			if rec.Code != want {
				t.Fatalf("status %d, want %d", rec.Code, want)
			}
		})
	}
}

func TestLoadFile(t *testing.T) {
	t.Parallel()
	path := filepath.Join(t.TempDir(), "token")
	if err := os.WriteFile(path, []byte("short\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if _, err := LoadFile(path); err == nil {
		t.Fatal("expected short token error")
	}
	token := "0123456789abcdef0123456789abcdef"
	if err := os.WriteFile(path, []byte(token+"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	got, err := LoadFile(path)
	if err != nil || got != token {
		t.Fatalf("got %q, %v", got, err)
	}
}

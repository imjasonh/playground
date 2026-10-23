package scenario

import (
	"context"
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"strconv"
	"sync"
	"testing"
	"time"
)

func TestSoakWithoutSimulator(t *testing.T) {
	var mu sync.Mutex
	items := map[int64]string{}
	var next int64
	var verified bool
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch {
		case r.Method == http.MethodPost && r.URL.Path == "/items":
			body, _ := io.ReadAll(r.Body)
			mu.Lock()
			next++
			id := next
			items[id] = string(body)
			mu.Unlock()
			w.WriteHeader(http.StatusCreated)
			json.NewEncoder(w).Encode(map[string]any{"id": id})
		case r.Method == http.MethodGet && len(r.URL.Path) > len("/items/"):
			id, _ := strconv.ParseInt(r.URL.Path[len("/items/"):], 10, 64)
			mu.Lock()
			body, ok := items[id]
			mu.Unlock()
			if !ok {
				http.NotFound(w, r)
				return
			}
			json.NewEncoder(w).Encode(map[string]string{"body": body})
		default:
			http.NotFound(w, r)
		}
	}))
	defer srv.Close()

	res, err := Soak(t.Context(), SoakConfig{
		URL:      srv.URL,
		Duration: 300 * time.Millisecond,
		Writers:  2,
		Readers:  2,
		BodySize: 8,
		BeforeVerify: func(context.Context) error {
			verified = true
			return nil
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if !verified {
		t.Fatal("BeforeVerify did not run")
	}
	if res.Acked == 0 {
		t.Fatal("no acknowledged writes")
	}
	if res.Integrity != "skipped" {
		t.Fatalf("integrity = %q, want skipped", res.Integrity)
	}
	if len(res.Violations) > 0 {
		t.Fatalf("violations: %v", res.Violations)
	}
	if res.Missing != 0 || res.Mismatched != 0 {
		t.Fatalf("missing %d mismatched %d", res.Missing, res.Mismatched)
	}
}

package attest

import (
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strings"
	"sync"
	"testing"
	"time"
)

func TestGCSStoreChallengeAndDeviceRoundTrip(t *testing.T) {
	type obj struct {
		data []byte
		gen  int
	}
	var mu sync.Mutex
	objects := make(map[string]obj)
	nextGen := 1

	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		defer mu.Unlock()
		switch r.Method {
		case http.MethodPost:
			name := r.URL.Query().Get("name")
			data, _ := io.ReadAll(r.Body)
			objects[name] = obj{data: data, gen: nextGen}
			nextGen++
			w.WriteHeader(http.StatusOK)
		case http.MethodGet:
			prefix := "/storage/v1/b/test-bucket/o/"
			name, _ := url.PathUnescape(strings.TrimPrefix(r.URL.Path, prefix))
			o, ok := objects[name]
			if !ok {
				http.NotFound(w, r)
				return
			}
			w.Header().Set("X-Goog-Generation", fmt.Sprintf("%d", o.gen))
			_, _ = w.Write(o.data)
		case http.MethodDelete:
			prefix := "/storage/v1/b/test-bucket/o/"
			name, _ := url.PathUnescape(strings.TrimPrefix(r.URL.Path, prefix))
			o, ok := objects[name]
			if !ok {
				http.NotFound(w, r)
				return
			}
			if want := r.URL.Query().Get("ifGenerationMatch"); want != "" && want != fmt.Sprintf("%d", o.gen) {
				w.WriteHeader(http.StatusPreconditionFailed)
				return
			}
			delete(objects, name)
			w.WriteHeader(http.StatusNoContent)
		default:
			w.WriteHeader(http.StatusMethodNotAllowed)
		}
	}))
	defer srv.Close()

	store := &GCSStore{
		Bucket:  "test-bucket",
		Prefix:  "attest",
		BaseURL: srv.URL,
	}

	now := time.Date(2026, 11, 22, 12, 0, 0, 0, time.UTC)
	if err := store.PutChallenge("chal-1", now.Add(time.Minute)); err != nil {
		t.Fatalf("PutChallenge: %v", err)
	}
	if err := store.ConsumeChallenge("chal-1", now.Add(10*time.Second)); err != nil {
		t.Fatalf("ConsumeChallenge first time: %v", err)
	}
	if err := store.ConsumeChallenge("chal-1", now.Add(11*time.Second)); err == nil {
		t.Fatalf("expected replay of consumed challenge to fail")
	}

	if err := store.PutChallenge("chal-expired", now.Add(-time.Second)); err != nil {
		t.Fatalf("PutChallenge expired: %v", err)
	}
	if err := store.ConsumeChallenge("chal-expired", now); err == nil {
		t.Fatalf("expected expired challenge to fail")
	}

	rec := &DeviceRecord{
		KeyID:    "key-abc",
		UserID:   "user-1",
		DeviceID: "dev-1",
		Counter:  7,
	}
	if err := store.PutDevice(rec); err != nil {
		t.Fatalf("PutDevice: %v", err)
	}
	got, err := store.GetDevice("key-abc")
	if err != nil || got == nil {
		t.Fatalf("GetDevice: got=%v err=%v", got, err)
	}
	if got.Counter != 7 || got.DeviceID != "dev-1" {
		t.Fatalf("unexpected device record: %+v", got)
	}
	missing, err := store.GetDevice("nonexistent")
	if err != nil || missing != nil {
		t.Fatalf("expected nil for missing device, got=%v err=%v", missing, err)
	}
}

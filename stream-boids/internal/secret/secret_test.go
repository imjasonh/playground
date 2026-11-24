package secret

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"errors"
	"hash/crc32"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

const value = "abcd-efgh-ijkl-mnop-qrst"

type fakeGCP struct {
	tokens   atomic.Int32
	accesses atomic.Int32
	payload  string
	crc      string
	status   int
	gotPath  atomic.Value
}

func (f *fakeGCP) servers(t *testing.T) *Manager {
	md := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Metadata-Flavor") != "Google" {
			http.Error(w, "missing Metadata-Flavor", http.StatusForbidden)
			return
		}
		switch r.URL.Path {
		case "/computeMetadata/v1/project/project-id":
			w.Write([]byte("my-proj"))
		case "/computeMetadata/v1/instance/service-accounts/default/token":
			n := f.tokens.Add(1)
			json.NewEncoder(w).Encode(map[string]any{
				"access_token": "tok-" + strconv.Itoa(int(n)), "expires_in": 3599, "token_type": "Bearer",
			})
		default:
			http.NotFound(w, r)
		}
	}))
	t.Cleanup(md.Close)
	sm := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		f.accesses.Add(1)
		f.gotPath.Store(r.URL.Path)
		if !strings.HasPrefix(r.Header.Get("Authorization"), "Bearer tok-") {
			http.Error(w, `{"error":{"code":401}}`, http.StatusUnauthorized)
			return
		}
		if f.status != 0 {
			http.Error(w, `{"error":{"message":"Permission denied on secret"}}`, f.status)
			return
		}
		json.NewEncoder(w).Encode(map[string]any{
			"name":    "projects/123/secrets/stream-key/versions/4",
			"payload": map[string]string{"data": f.payload, "dataCrc32c": f.crc},
		})
	}))
	t.Cleanup(sm.Close)
	return &Manager{API: sm.URL, Metadata: md.URL}
}

func encode(v string) (data, crc string) {
	return base64.StdEncoding.EncodeToString([]byte(v)),
		strconv.FormatUint(uint64(crc32.Checksum([]byte(v), crc32.MakeTable(crc32.Castagnoli))), 10)
}

func TestManagerReadsLatestVersion(t *testing.T) {
	f := &fakeGCP{}
	f.payload, f.crc = encode(value + "\n")
	m := f.servers(t)
	get := m.Secret("stream-key")
	for range 3 {
		got, err := get(t.Context())
		if err != nil {
			t.Fatal(err)
		}
		if got != value {
			t.Errorf("value = %q, want %q", got, value)
		}
	}
	if p := f.gotPath.Load(); p != "/v1/projects/my-proj/secrets/stream-key/versions/latest:access" {
		t.Errorf("path = %v", p)
	}
	if n := f.tokens.Load(); n != 1 {
		t.Errorf("fetched %d tokens, want 1 reused", n)
	}
	if n := f.accesses.Load(); n != 3 {
		t.Errorf("accessed %d times, want every call", n)
	}
}

func TestManagerFullResourceName(t *testing.T) {
	f := &fakeGCP{}
	f.payload, f.crc = encode(value)
	m := f.servers(t)
	if _, err := m.Secret("projects/other/secrets/k/versions/2")(t.Context()); err != nil {
		t.Fatal(err)
	}
	if p := f.gotPath.Load(); p != "/v1/projects/other/secrets/k/versions/2:access" {
		t.Errorf("path = %v", p)
	}
}

func TestManagerErrorsHideValue(t *testing.T) {
	for _, tc := range []struct {
		name string
		set  func(*fakeGCP)
		want string
	}{{
		name: "checksum",
		set:  func(f *fakeGCP) { f.payload, _ = encode(value); f.crc = "12345" },
		want: "checksum mismatch",
	}, {
		name: "denied",
		set:  func(f *fakeGCP) { f.status = http.StatusForbidden },
		want: "403 Forbidden",
	}, {
		name: "empty",
		set:  func(f *fakeGCP) { f.payload, f.crc = encode("  \n") },
		want: "is empty",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := &fakeGCP{}
			tc.set(f)
			_, err := f.servers(t).Secret("stream-key")(t.Context())
			if err == nil {
				t.Fatal("no error")
			}
			if !strings.Contains(err.Error(), tc.want) {
				t.Errorf("error %q lacks %q", err, tc.want)
			}
			if strings.Contains(err.Error(), value) || strings.Contains(err.Error(), f.payload) && f.payload != "" {
				t.Errorf("error %q reveals the value", err)
			}
		})
	}
}

func TestManagerNoMetadataServer(t *testing.T) {
	m := &Manager{Metadata: "http://127.0.0.1:1", Client: &http.Client{Timeout: time.Second}}
	if _, err := m.Secret("stream-key")(t.Context()); err == nil || !strings.Contains(err.Error(), "project ID") {
		t.Errorf("error = %v, want one about the project ID", err)
	}
}

func TestFile(t *testing.T) {
	dir := t.TempDir()
	p := filepath.Join(dir, "key")
	os.WriteFile(p, []byte("  "+value+"\n"), 0o600)
	got, err := File(p)(t.Context())
	if err != nil || got != value {
		t.Errorf("File = %q, %v", got, err)
	}
	os.WriteFile(p, []byte("\n"), 0o600)
	if _, err := File(p)(t.Context()); err == nil {
		t.Error("empty file accepted")
	}
	if _, err := File(filepath.Join(dir, "missing"))(t.Context()); err == nil {
		t.Error("missing file accepted")
	}
}

func TestCached(t *testing.T) {
	var calls atomic.Int32
	fail := true
	fn := Cached(func(context.Context) (string, error) {
		calls.Add(1)
		if fail {
			return "", errors.New("down")
		}
		return value, nil
	}, time.Hour)
	if _, err := fn(t.Context()); err == nil {
		t.Fatal("error not returned")
	}
	fail = false
	for range 3 {
		if v, err := fn(t.Context()); err != nil || v != value {
			t.Fatalf("Cached = %q, %v", v, err)
		}
	}
	if n := calls.Load(); n != 2 {
		t.Errorf("called %d times, want 2 (the error is not cached)", n)
	}
}

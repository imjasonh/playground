package main

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
)

func newEvent(namespace, name, uid, reason string, last time.Time) *Event {
	e := &Event{Object: kube.Meta(name, nil), Reason: reason, Message: reason + " the image", Type: "Normal", Count: 1, LastTimestamp: last}
	e.Namespace, e.UID = namespace, uid
	e.InvolvedObject = ObjectReference{Kind: "Pod", Name: "web-1"}
	return e
}

func TestKeepsAndServesEvents(t *testing.T) {
	dir := t.TempDir()
	t0 := time.Date(2026, 10, 4, 12, 0, 0, 0, time.UTC)
	pulled := newEvent("team", "web-1.b", "uid-b", "Pulled", t0.Add(time.Minute))
	pulling := newEvent("team", "web-1.a", "uid-a", "Pulling", t0)
	elsewhere := newEvent("other", "db-1.a", "uid-c", "Pulling", t0)
	ci := kube.UserInfo{Username: "system:serviceaccount:team:ci"}
	ctx, _ := kube.Fake(t.Context(), pulled, pulling, elsewhere,
		kube.FakeToken{Token: "ci", User: ci, Audiences: []string{"eventlog"}},
		kube.FakeToken{Token: "ci-elsewhere", User: ci, Audiences: []string{"other"}},
		kube.FakeToken{Token: "admin", User: kube.UserInfo{Username: "kubernetes-admin"}, Audiences: []string{"eventlog"}},
		kube.FakeToken{Token: "quiet", User: kube.UserInfo{Username: "system:serviceaccount:quiet:ci"}, Audiences: []string{"eventlog"}},
	)
	l := &eventLog{dir: &dir}
	for _, e := range []*Event{pulled, pulling, elsewhere} {
		if err := l.Reconcile(ctx, e); err != nil {
			t.Fatal(err)
		}
	}
	pulling.Count = 2
	if err := l.Reconcile(ctx, pulling); err != nil {
		t.Fatal(err)
	}
	if b, err := os.ReadFile(filepath.Join(dir, "team", "uid-a.json")); err != nil || !strings.Contains(string(b), `"count":2`) {
		t.Errorf("the copy of a changed Event = %s, %v", b, err)
	}

	audience := "eventlog"
	h := (&api{dir: &dir, audience: &audience}).handler()
	get := func(path, token string) *httptest.ResponseRecorder {
		req := httptest.NewRequest(http.MethodGet, path, nil).WithContext(ctx)
		if token != "" {
			req.Header.Set("Authorization", "Bearer "+token)
		}
		w := httptest.NewRecorder()
		h.ServeHTTP(w, req)
		return w
	}
	w := get("/events/team", "ci")
	var records []Record
	if err := json.Unmarshal(w.Body.Bytes(), &records); w.Code != http.StatusOK || err != nil {
		t.Fatalf("GET /events/team = %d %s", w.Code, w.Body)
	}
	if len(records) != 2 || records[0].Name != "web-1.a" || records[0].Count != 2 || records[1].Reason != "Pulled" || records[1].Object.Name != "web-1" {
		t.Errorf("records = %+v, want the two Events in team, oldest first", records)
	}
	for _, tc := range []struct {
		path, token string
		code        int
		body        string
	}{
		{"/events/team", "", http.StatusUnauthorized, "no token"},
		{"/events/team", "ci-elsewhere", http.StatusUnauthorized, "is invalid for the target audiences"},
		{"/events/other", "ci", http.StatusForbidden, "can't read the Events of other"},
		{"/events/team", "admin", http.StatusForbidden, "kubernetes-admin can't read"},
		{"/events/quiet", "quiet", http.StatusOK, "[]\n"},
	} {
		if w := get(tc.path, tc.token); w.Code != tc.code || !strings.Contains(w.Body.String(), tc.body) {
			t.Errorf("GET %s with %q = %d %q, want %d %q", tc.path, tc.token, w.Code, w.Body, tc.code, tc.body)
		}
	}
}

func TestSkipsCopiesThatCantBeRead(t *testing.T) {
	dir := t.TempDir()
	t0 := time.Date(2026, 10, 4, 12, 0, 0, 0, time.UTC)
	kept := newEvent("team", "web-1.a", "uid-a", "Pulling", t0)
	damaged := newEvent("team", "web-1.b", "uid-b", "Pulled", t0.Add(time.Minute))
	ctx, _ := kube.Fake(t.Context(), kept, damaged,
		kube.FakeToken{Token: "ci", User: kube.UserInfo{Username: "system:serviceaccount:team:ci"}, Audiences: []string{"eventlog"}})
	l := &eventLog{dir: &dir}
	for _, e := range []*Event{kept, damaged} {
		if err := l.Reconcile(ctx, e); err != nil {
			t.Fatal(err)
		}
	}
	team := filepath.Join(dir, "team")
	// A copy emptied by a crash, one cut short, and one that isn't a file.
	for name, data := range map[string]string{"uid-b.json": "", "uid-gone.json": `{"name":"web-1.gone","obj`} {
		if err := os.WriteFile(filepath.Join(team, name), []byte(data), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.Mkdir(filepath.Join(team, "uid-dir.json"), 0o700); err != nil {
		t.Fatal(err)
	}

	audience := "eventlog"
	h := (&api{dir: &dir, audience: &audience}).handler()
	names := func() []string {
		t.Helper()
		req := httptest.NewRequest(http.MethodGet, "/events/team", nil).WithContext(ctx)
		req.Header.Set("Authorization", "Bearer ci")
		w := httptest.NewRecorder()
		h.ServeHTTP(w, req)
		var records []Record
		if err := json.Unmarshal(w.Body.Bytes(), &records); w.Code != http.StatusOK || err != nil {
			t.Fatalf("GET /events/team = %d %s", w.Code, w.Body)
		}
		var names []string
		for _, r := range records {
			names = append(names, r.Name)
		}
		return names
	}
	if got := names(); !slices.Equal(got, []string{"web-1.a"}) {
		t.Errorf("records = %q, want only the copy that can be read", got)
	}

	if err := l.Reconcile(ctx, damaged); err != nil {
		t.Fatal(err)
	}
	if got := names(); !slices.Equal(got, []string{"web-1.a", "web-1.b"}) {
		t.Errorf("after a reconcile of the damaged copy's Event, records = %q", got)
	}
	entries, err := os.ReadDir(team)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range entries {
		if strings.HasPrefix(e.Name(), ".event-") {
			t.Errorf("a temporary file is left: %s", e.Name())
		}
	}
}

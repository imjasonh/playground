package gateway

import (
	"bytes"
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/session"
)

func TestControlFreezeTimeoutKicksSession(t *testing.T) {
	t.Parallel()
	registry := session.NewRegistry()
	id, err := registry.Admit("alice", "myapp", "gabc")
	if err != nil {
		t.Fatal(err)
	}
	sessionCtx, cancelSession := context.WithCancel(context.Background())
	registry.BindCancel(id, cancelSession)
	hub := &Hub{Sessions: registry}
	mux := http.NewServeMux()
	(&ControlHandler{Hub: hub, MaxFreeze: 25 * time.Millisecond}).Mount(mux)

	body, _ := json.Marshal(freezeRequest{
		User: "alice", App: "myapp", Gen: "gabc", TimeoutMS: 10,
	})
	req := httptest.NewRequest(http.MethodPost, "/v1/sessions/freeze", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("freeze: %d %s", rec.Code, rec.Body.String())
	}
	select {
	case <-sessionCtx.Done():
	case <-time.After(time.Second):
		t.Fatal("freeze timeout did not force reconnect")
	}
	registry.Release(id)
}

func TestExpiredFreezeTokenNeverKicksLaterReconnect(t *testing.T) {
	t.Parallel()
	registry := session.NewRegistry()
	oldID, err := registry.Admit("alice", "myapp", "gabc")
	if err != nil {
		t.Fatal(err)
	}
	hub := &Hub{Sessions: registry}
	mux := http.NewServeMux()
	(&ControlHandler{Hub: hub, MaxFreeze: 40 * time.Millisecond}).Mount(mux)
	body, _ := json.Marshal(freezeRequest{User: "alice", App: "myapp", Gen: "gabc", TimeoutMS: 30})
	req := httptest.NewRequest(http.MethodPost, "/v1/sessions/freeze", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("freeze: %d %s", rec.Code, rec.Body.String())
	}
	registry.Release(oldID)

	newID, err := registry.Admit("alice", "myapp", "gabc")
	if err != nil {
		t.Fatal(err)
	}
	newCtx, cancel := context.WithCancel(context.Background())
	defer cancel()
	registry.BindCancel(newID, cancel)
	time.Sleep(75 * time.Millisecond)
	select {
	case <-newCtx.Done():
		t.Fatal("old freeze token kicked a later reconnect")
	default:
	}
	registry.Release(newID)
}

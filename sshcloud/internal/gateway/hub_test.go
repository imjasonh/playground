package gateway

import (
	"context"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestHubJoinMenuFortuneBusy(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	h := &Hub{Store: store.NewMemory(), Sessions: session.NewRegistry()}

	// Unknown key → join
	r, err := h.HandleConnect(ctx, Connect{SSHUser: "anything", KeyFingerprint: "SHA256:new"})
	if err != nil || r.Action != ActionJoin {
		t.Fatalf("got %+v %v", r, err)
	}

	if err := h.Store.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}

	// Bare local username → menu
	r, err = h.HandleConnect(ctx, Connect{SSHUser: "alice", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionMenu {
		t.Fatalf("got %+v %v", r, err)
	}

	// Deep link fortune → proxy + lazy create
	r, err = h.HandleConnect(ctx, Connect{SSHUser: "fortune", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionProxyApp || r.App != "fortune" || r.Session == "" {
		t.Fatalf("got %+v %v", r, err)
	}
	sess := r.Session

	// Second connect → reject busy
	r, err = h.HandleConnect(ctx, Connect{SSHUser: "fortune", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionRejectBusy {
		t.Fatalf("got %+v %v", r, err)
	}

	h.ReleaseSession(sess)
	r, err = h.HandleConnect(ctx, Connect{SSHUser: "fortune", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionProxyApp {
		t.Fatalf("got %+v %v", r, err)
	}
	h.ReleaseSession(r.Session)
}

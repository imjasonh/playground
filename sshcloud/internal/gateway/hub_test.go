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

func TestHubPinsActiveGenAndAllowsDrainPeer(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	digest := "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
	if err := st.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "myapp",
		Image: "ghcr.io/example/app@sha256:" + digest,
		Tier:  "tiny", ActiveGen: "gnew", DrainingGen: "gold",
		DrainUntilUnix: 9999999999,
	}); err != nil {
		t.Fatal(err)
	}
	h := &Hub{Store: st, Sessions: session.NewRegistry()}
	old, err := h.Sessions.Admit("alice", "myapp", "gold")
	if err != nil {
		t.Fatal(err)
	}
	r, err := h.HandleConnect(ctx, Connect{SSHUser: "myapp", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionProxyApp || r.Gen != "gnew" {
		t.Fatalf("got %+v %v", r, err)
	}
	r2, err := h.HandleConnect(ctx, Connect{SSHUser: "myapp", KeyFingerprint: "SHA256:alice"})
	if err != nil || r2.Action != ActionRejectBusy {
		t.Fatalf("third connect: %+v %v", r2, err)
	}
	h.ReleaseSession(r.Session)
	h.Sessions.Release(old)
}

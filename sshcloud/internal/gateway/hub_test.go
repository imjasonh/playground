package gateway

import (
	"context"
	"errors"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/access"
	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestHubJoinMenuDeployedAppBusy(t *testing.T) {
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

	// Undeployed fortune → menu (not a platform snowflake)
	r, err = h.HandleConnect(ctx, Connect{SSHUser: "fortune", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != ActionMenu {
		t.Fatalf("undeployed fortune: %+v %v", r, err)
	}

	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	if err := h.Store.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "fortune",
		Image: "ghcr.io/example/fortune@sha256:" + digest,
		Tier:  "tiny",
	}); err != nil {
		t.Fatal(err)
	}

	// Deep link fortune after deploy → proxy
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

func TestAdmissionPinsGenerationImageAndTier(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	oldImage := "ghcr.io/example/app@sha256:" + strings.Repeat("a", 64)
	if err := st.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "myapp", Image: oldImage, Tier: "tiny", ActiveGen: "gold",
	}); err != nil {
		t.Fatal(err)
	}
	sessions := session.NewRegistry()
	h := &Hub{Store: st, Sessions: sessions, Cutover: cutover.New(st, sessions, nil)}
	res, err := h.HandleConnect(ctx, Connect{SSHUser: "myapp", KeyFingerprint: "SHA256:alice"})
	if err != nil {
		t.Fatal(err)
	}

	app, _ := st.GetApp(ctx, "alice", "myapp")
	app.Image = "ghcr.io/example/app@sha256:" + strings.Repeat("b", 64)
	app.Tier = "small"
	app.ActiveGen = "gnew"
	if err := st.UpsertApp(ctx, *app); err != nil {
		t.Fatal(err)
	}
	if res.Gen != "gold" || res.Image != oldImage || res.Tier != "tiny" {
		t.Fatalf("admission spec changed after deploy: %+v", res)
	}
	h.ReleaseSession(res.Session)
}

func TestHubReadinessIncludesPolicyBackendAndRuntime(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	h := &Hub{
		Store:  store.NewMemory(),
		Access: access.StaticSource{Policy: access.LocalDevelopmentPolicy()},
		BackendReady: func(context.Context) error {
			return nil
		},
		RuntimeReady: func() error {
			return nil
		},
	}
	if err := h.Ready(ctx); err != nil {
		t.Fatalf("ready dependencies: %v", err)
	}

	h.Access = accessSourceFunc(func() (access.Policy, error) {
		return access.Policy{}, errors.New("policy lease expired")
	})
	if err := h.Ready(ctx); err == nil || !strings.Contains(err.Error(), "access policy") {
		t.Fatalf("policy readiness error = %v", err)
	}

	h.Access = access.StaticSource{Policy: access.LocalDevelopmentPolicy()}
	h.BackendReady = func(context.Context) error { return errors.New("orchestrator unavailable") }
	if err := h.Ready(ctx); err == nil || !strings.Contains(err.Error(), "backend") {
		t.Fatalf("backend readiness error = %v", err)
	}

	h.BackendReady = nil
	h.RuntimeReady = func() error { return errors.New("control bundle lease expired") }
	if err := h.Ready(ctx); err == nil || !strings.Contains(err.Error(), "control bundle") {
		t.Fatalf("runtime readiness error = %v", err)
	}
}

type accessSourceFunc func() (access.Policy, error)

func (f accessSourceFunc) Load() (access.Policy, error) {
	return f()
}

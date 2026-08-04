package store

import (
	"context"
	"testing"
)

func TestMemoryJoinAndDemo(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	m := NewMemory()

	u, err := m.LookupUserByKey(ctx, "SHA256:abc")
	if err != nil || u != nil {
		t.Fatalf("expected no user, got %v %v", u, err)
	}
	if err := m.CreateUser(ctx, "alice", "SHA256:abc"); err != nil {
		t.Fatal(err)
	}
	u, err = m.LookupUserByKey(ctx, "SHA256:abc")
	if err != nil || u == nil || u.ID != "alice" {
		t.Fatalf("got %v %v", u, err)
	}

	has, err := m.HasApp(ctx, "alice", "fortune")
	if err != nil || has {
		t.Fatalf("fortune should not exist yet: %v %v", has, err)
	}
	if err := m.EnsureDemoApp(ctx, "alice", "fortune"); err != nil {
		t.Fatal(err)
	}
	has, err = m.HasApp(ctx, "alice", "fortune")
	if err != nil || !has {
		t.Fatalf("expected fortune: %v %v", has, err)
	}
	if !IsPlatformDemo("fortune") || IsPlatformDemo("myapp") {
		t.Fatal("demo map unexpected")
	}
}

func TestMemoryUpsertApp(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	m := NewMemory()
	if err := m.CreateUser(ctx, "alice", "SHA256:abc"); err != nil {
		t.Fatal(err)
	}
	if err := m.UpsertApp(ctx, App{
		Owner: "alice", Name: "myapp",
		Image: "ghcr.io/me/app@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		Tier:  "small", SessionStrategy: StrategyKick,
	}); err != nil {
		t.Fatal(err)
	}
	app, err := m.GetApp(ctx, "alice", "myapp")
	if err != nil || app == nil || app.Tier != "small" || app.SessionStrategy != StrategyKick {
		t.Fatalf("got %+v %v", app, err)
	}
	if err := m.UpsertApp(ctx, App{Owner: "alice", Name: "fortune", Image: "x@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"}); err == nil {
		t.Fatal("expected reject platform demo name")
	}
}

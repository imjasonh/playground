package store

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"
)

func TestMemoryConformance(t *testing.T) {
	t.Parallel()
	runStoreConformance(t, NewMemory())
}

func TestFirestoreConformance(t *testing.T) {
	if os.Getenv("FIRESTORE_EMULATOR_HOST") == "" {
		t.Skip("FIRESTORE_EMULATOR_HOST not set; start the emulator to run this test")
	}
	ctx := context.Background()
	project := os.Getenv("FIRESTORE_PROJECT_ID")
	if project == "" {
		project = "sshcloud-test"
	}
	fs, err := NewFirestore(ctx, project)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = fs.Close() })
	runStoreConformance(t, fs)
}

func runStoreConformance(t *testing.T, s Store) {
	t.Helper()
	ctx := context.Background()
	user := fmt.Sprintf("u%d", time.Now().UnixNano())
	keyA := "SHA256:" + user + "-a"
	keyB := "SHA256:" + user + "-b"

	u, err := s.LookupUserByKey(ctx, keyA)
	if err != nil || u != nil {
		t.Fatalf("expected no user: %v %v", u, err)
	}
	if err := s.CreateUser(ctx, user, keyA); err != nil {
		t.Fatal(err)
	}
	if err := s.CreateUser(ctx, user, "SHA256:other"); err == nil {
		t.Fatal("expected duplicate user error")
	}
	if err := s.CreateUser(ctx, user+"x", keyA); err == nil {
		t.Fatal("expected duplicate key error")
	}
	u, err = s.LookupUserByKey(ctx, keyA)
	if err != nil || u == nil || u.ID != user {
		t.Fatalf("lookup: %v %v", u, err)
	}
	if err := s.AddKey(ctx, user, keyB); err != nil {
		t.Fatal(err)
	}
	u, err = s.LookupUserByKey(ctx, keyB)
	if err != nil || u == nil || u.ID != user {
		t.Fatalf("second key: %v %v", u, err)
	}

	has, err := s.HasApp(ctx, user, "fortune")
	if err != nil || has {
		t.Fatalf("fortune should be absent until deployed: %v %v", has, err)
	}

	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	if err := s.UpsertApp(ctx, App{
		Owner: user, Name: "fortune",
		Image: "ghcr.io/me/fortune@sha256:" + digest,
		Tier:  "tiny", SessionStrategy: StrategyDrain,
	}); err != nil {
		t.Fatal(err)
	}
	fortune, err := s.GetApp(ctx, user, "fortune")
	if err != nil || fortune == nil || fortune.Image == "" {
		t.Fatalf("deployed fortune: %+v %v", fortune, err)
	}

	if err := s.UpsertApp(ctx, App{
		Owner: user, Name: "myapp",
		Image: "ghcr.io/me/app@sha256:" + digest,
		Tier:  "small", SessionStrategy: StrategyKick,
	}); err != nil {
		t.Fatal(err)
	}
	app, err := s.GetApp(ctx, user, "myapp")
	if err != nil || app == nil || app.Tier != "small" || app.SessionStrategy != StrategyKick {
		t.Fatalf("upserted app: %+v %v", app, err)
	}
	app.ActiveGen = "gnew"
	app.DrainingGen = "gold"
	app.DrainUntilUnix = 1700000000
	app.PreviousImage = "old@sha256:" + digest
	if err := s.UpsertApp(ctx, *app); err != nil {
		t.Fatal(err)
	}
	app, err = s.GetApp(ctx, user, "myapp")
	if err != nil || app == nil || app.ActiveGen != "gnew" || app.DrainingGen != "gold" || app.DrainUntilUnix != 1700000000 {
		t.Fatalf("gen fields: %+v %v", app, err)
	}

	apps, err := s.ListApps(ctx, user)
	if err != nil {
		t.Fatal(err)
	}
	if len(apps) < 2 {
		t.Fatalf("list apps: %+v", apps)
	}
}
